#!/usr/bin/env python3
"""
Voyz Automation Web Panel — FINAL (Render-ready)
- NextCaptcha key panel se change ho sakti hai (data/settings.json)
- Default: script wali key (agar panel se change na karein)
- eventlet monkey patch + async_mode='eventlet'
- socketio.start_background_task fixed for Render
"""
import eventlet
eventlet.monkey_patch()

import sys
sys.path.insert(0, "/root/.local/lib/python3.12/site-packages")

import os, re, json, time, random, base64, html as html_mod, urllib.parse, threading
from datetime import datetime, timezone
from collections import Counter, OrderedDict
from typing import Optional, List, Dict
from queue import Queue
from concurrent.futures import ThreadPoolExecutor, as_completed

import requests
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry

from flask import Flask, request, jsonify, send_from_directory
from flask_socketio import SocketIO, emit

# ============================
# PATHS & CONFIG
# ============================
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
DATA_DIR = os.environ.get("DATA_DIR", os.path.join(BASE_DIR, "data"))
STATIC_DIR = os.path.join(BASE_DIR, "static")
os.makedirs(DATA_DIR, exist_ok=True)
os.makedirs(STATIC_DIR, exist_ok=True)

SAVED_ACCOUNTS_JSON = os.path.join(DATA_DIR, "saved_accounts.json")
ACCOUNTS_LOG_TXT = os.path.join(DATA_DIR, "accounts_log.txt")
SESSIONS_FILE = os.path.join(DATA_DIR, "sessions.json")
PANELS_FILE = os.path.join(DATA_DIR, "panels.json")
DUPLICATE_NUMBERS_TXT = os.path.join(DATA_DIR, "duplicate_numbers.txt")
OTP_FAIL_COUNTS_JSON = os.path.join(DATA_DIR, "otp_fail_counts.json")
SETTINGS_FILE = os.path.join(DATA_DIR, "settings.json")

PASSWORD = "Jjaideep1,@"
SURVEY_ID = "5382"
DEFAULT_REFERRAL_CODE = "VS6K3T"
PARALLEL_SURVEYS = 5
WITHDRAW_AMOUNT = 5
BATCH_SIZE = 10

OTP_MIN_SEND_GAP = 0.3
OTP_JITTER_MIN   = 0.1
OTP_JITTER_MAX   = 0.9
OTP_RATE_LIMIT_BACKOFF = (1.0, 3.0)
OTP_RATE_LIMIT_MAX_ATTEMPTS = 20

PROXIES_TXT = os.path.join(DATA_DIR, "proxies.txt")

DEVICE_FETCH_THREADS = 200
FIREBASE_READ_SEM    = 8
OTP_POLL_TIMEOUT     = 45
OTP_POLL_INTERVAL    = 1.2

UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/140.0.0.0 Safari/537.36")

OTP_PATTERN = re.compile(r"(?<!\d)(\d{6})(?!\d)")
PHONE_PATTERNS = [
    re.compile(r"\b(?:\+91|91|0)?([6-9]\d{9})\b"),
    re.compile(r"\b(?:phone|mobile|number|contact)[\s:]*([6-9]\d{9})\b", re.I),
    re.compile(r"[^0-9]([6-9]\d{9})[^0-9]"),
]

DEFAULT_NEXTCAPTCHA_KEY = "next_b24424eade14745250ee821c36b037d871"


def get_random_proxy():
    if not os.path.exists(PROXIES_TXT):
        return None
    try:
        with open(PROXIES_TXT, "r") as f:
            proxies = [l.strip() for l in f if l.strip() and not l.startswith("#")]
        if proxies:
            proxy = random.choice(proxies)
            if not proxy.startswith("http"):
                proxy = f"http://{proxy}"
            return {"http": proxy, "https": proxy}
    except Exception as e:
        print(f"Proxy read error: {e}")
    return None


# ============================
# HELPERS (JSON)
# ============================
def load_json(path, default=None):
    if default is None: default = {}
    if not os.path.exists(path): return default
    try:
        with open(path) as f: return json.load(f)
    except Exception: return default


def save_json(path, data):
    with open(path, "w") as f: json.dump(data, f, indent=2)


def load_settings():
    return load_json(SETTINGS_FILE, {})


def save_settings(data):
    save_json(SETTINGS_FILE, data)


# ============================
# NEXTCAPTCHA
# ============================
_saved_settings = load_settings()
NEXTCAPTCHA_KEY = (
    _saved_settings.get("nextcaptcha_key")
    or os.environ.get("NEXTCAPTCHA_KEY")
    or DEFAULT_NEXTCAPTCHA_KEY
).strip()

NEXTCAPTCHA_CREATE = os.environ.get("NEXTCAPTCHA_CREATE", "https://api.nextcaptcha.com/createTask")
NEXTCAPTCHA_RESULT = os.environ.get("NEXTCAPTCHA_RESULT", "https://api.nextcaptcha.com/getTaskResult")

SOLVERCF_KEY    = NEXTCAPTCHA_KEY
SOLVERCF_CREATE = NEXTCAPTCHA_CREATE
SOLVERCF_RESULT = NEXTCAPTCHA_RESULT

VOYZ_RECAPTCHA_SITEKEY = "6Ld-49IoAAAAANjhCDH2AKKaLGJHDNaHiISHLnMT"
VOYZ_PAGE_URL = "https://voyz.store/"
VOYZ_PAGE_ACTION_REGISTER = os.environ.get("VOYZ_PAGE_ACTION_REGISTER", "register")
VOYZ_PAGE_ACTION_LOGIN = os.environ.get("VOYZ_PAGE_ACTION_LOGIN", "login")
SOLVERCF_TIMEOUT = int(os.environ.get("SOLVERCF_TIMEOUT", "90"))
SOLVERCF_TOKEN_TTL = int(os.environ.get("SOLVERCF_TOKEN_TTL", "100"))
RECAPTCHA_V2_API_DOMAIN = os.environ.get("RECAPTCHA_V2_API_DOMAIN", "google.com").strip()
RECAPTCHA_V2_INVISIBLE = os.environ.get("RECAPTCHA_V2_INVISIBLE", "false").lower() == "true"

_token_solve_lock = threading.Lock()
_token_cache_lock = threading.Lock()
_rejected_lock    = threading.Lock()
_token_cache      = {"token": None, "user_agent": None, "fetched_at": 0}
_rejected_tokens  = set()

_otp_send_lock = threading.Lock()
_otp_last_send_ts = [0.0]


def _stagger_otp_send():
    with _otp_send_lock:
        now = time.time()
        elapsed = now - _otp_last_send_ts[0]
        base_wait = max(0.0, OTP_MIN_SEND_GAP - elapsed)
        jitter = random.uniform(OTP_JITTER_MIN, OTP_JITTER_MAX)
        total_wait = base_wait + jitter
        _otp_last_send_ts[0] = now + total_wait
    if total_wait > 0:
        time.sleep(total_wait)


# ============================
# APP STATE
# ============================
app = Flask(__name__, static_folder=STATIC_DIR)
app.config["SECRET_KEY"] = "voyz-panel-secret"
socketio = SocketIO(app, cors_allowed_origins="*", async_mode="eventlet")

state_lock = threading.Lock()
session_file_lock = threading.Lock()
accounts_lock = threading.Lock()

state = {
    "running": False, "mode": None, "target": 10,
    "referral_code": DEFAULT_REFERRAL_CODE,
    "panels": [], "current_panel_idx": 0,
    "success_count": 0, "failed_count": 0, "no_otp_count": 0, "processed": 0,
    "queue_size": 0, "active_workers": 0,
    "logs": [], "recent_accounts": [], "numbers_found": [],
    "solvercf_configured": bool(SOLVERCF_KEY),
    "anticaptcha_balance": None,
    "stop_event": threading.Event(),
}
survey_queue = Queue()

_panel_cache = {}
_panel_cache_lock = threading.Lock()
_firebase_sem      = threading.Semaphore(FIREBASE_READ_SEM)
_panel_fetch_sem   = threading.Semaphore(60)


# ============================
# HELPERS
# ============================
def create_retry_session():
    session = requests.Session()
    retry = Retry(total=3, connect=3, read=3, backoff_factor=0.5,
                  status_forcelist=[429, 500, 502, 503, 504],
                  allowed_methods=frozenset(["GET", "POST"]))
    adapter = HTTPAdapter(max_retries=retry)
    session.mount("https://", adapter)
    session.mount("http://", adapter)
    proxy = get_random_proxy()
    if proxy:
        session.proxies.update(proxy)
    return session


def emit_log(message, log_type="info"):
    entry = {"timestamp": datetime.now().strftime("%H:%M:%S"),
             "message": message, "type": log_type}
    with state_lock:
        state["logs"].append(entry)
        if len(state["logs"]) > 500:
            state["logs"] = state["logs"][-400:]
    socketio.emit("log", entry)


def emit_status():
    with state_lock:
        payload = {
            "running": state["running"], "mode": state["mode"],
            "target": state["target"], "referral_code": state["referral_code"],
            "anticaptcha_balance": state.get("anticaptcha_balance"),
            "token_service_ok": state.get("solvercf_configured"),
            "solvercf_configured": state.get("solvercf_configured"),
            "success_count": state["success_count"], "failed_count": state["failed_count"],
            "no_otp_count": state["no_otp_count"], "processed": state["processed"],
            "queue_size": survey_queue.qsize(),
            "active_workers": state["active_workers"],
            "panels": state["panels"], "current_panel_idx": state["current_panel_idx"],
            "numbers_found": state["numbers_found"][-30:],
            "recent_accounts": state["recent_accounts"][-15:],
        }
    socketio.emit("status", payload)


def load_panels():
    data = load_json(PANELS_FILE, {"panels": []})
    with state_lock: state["panels"] = data.get("panels", [])
    return state["panels"]


def save_panels():
    with state_lock: panels = list(state["panels"])
    save_json(PANELS_FILE, {"panels": panels})


# ============================
# TOKEN CACHE
# ============================
def invalidate_token_cache():
    with _token_cache_lock:
        _token_cache.update({"token": None, "user_agent": None, "fetched_at": 0})
    with _rejected_lock:
        _rejected_tokens.clear()


def _mark_token_rejected(token):
    if not token: return
    with _rejected_lock:
        _rejected_tokens.add(token)
        if len(_rejected_tokens) > 100:
            recent = list(_rejected_tokens)[-50:]
            _rejected_tokens.clear()
            _rejected_tokens.update(recent)


def _is_token_rejected(token):
    if not token: return False
    with _rejected_lock: return token in _rejected_tokens


def _get_cached_token():
    with _token_cache_lock:
        tok = _token_cache["token"]; ua = _token_cache["user_agent"]
        age = time.time() - _token_cache["fetched_at"]
    if tok and age < SOLVERCF_TOKEN_TTL and not _is_token_rejected(tok):
        return {"token": tok, "userAgent": ua, "age": age}
    return None


def solve_solvercf(page_action: str = None, force_fresh: bool = False) -> Optional[Dict]:
    if not SOLVERCF_KEY:
        emit_log("❌ NEXTCAPTCHA_KEY set nahi hai", "error"); return None

    if not force_fresh:
        cached = _get_cached_token()
        if cached:
            emit_log(f"♻️ Reusing v2 token (age={int(cached['age'])}s/{SOLVERCF_TOKEN_TTL}s)", "info")
            return {"token": cached["token"], "userAgent": cached["userAgent"]}

    with _token_solve_lock:
        if not force_fresh:
            cached = _get_cached_token()
            if cached:
                emit_log(f"♻️ (Locked) Using fresh token from sibling (age={int(cached['age'])}s)", "info")
                return {"token": cached["token"], "userAgent": cached["userAgent"]}
        if force_fresh:
            with _token_cache_lock:
                _token_cache.update({"token": None, "user_agent": None, "fetched_at": 0})

        task = {"type": "RecaptchaV2TaskProxyless", "websiteURL": VOYZ_PAGE_URL,
                "websiteKey": VOYZ_RECAPTCHA_SITEKEY, "apiDomain": RECAPTCHA_V2_API_DOMAIN}
        if RECAPTCHA_V2_INVISIBLE:
            task["isInvisible"] = True

        try:
            start = time.time()
            r = requests.post(SOLVERCF_CREATE, json={"clientKey": SOLVERCF_KEY, "task": task}, timeout=20)
            data = r.json() if r.status_code == 200 else {}
            if data.get("errorId", 1) != 0:
                err = data.get("errorDescription") or data.get("errorCode") or f"HTTP {r.status_code}"
                emit_log(f"⚠️ createTask failed: {err}", "error"); return None
            task_id = data.get("taskId")
            if not task_id:
                emit_log("⚠️ createTask returned no taskId", "error"); return None
        except Exception as e:
            emit_log(f"⚠️ createTask exception: {str(e)[:150]}", "error"); return None

        emit_log(f"🧩 v2 task id={task_id} (invisible={RECAPTCHA_V2_INVISIBLE}) — polling…", "info")
        deadline = time.time() + SOLVERCF_TIMEOUT
        while time.time() < deadline:
            time.sleep(2)
            try:
                rr = requests.post(SOLVERCF_RESULT,
                                   json={"clientKey": SOLVERCF_KEY, "taskId": task_id}, timeout=15)
                rd = rr.json() if rr.status_code == 200 else {}
                status = rd.get("status")
                if status == "ready":
                    sol = rd.get("solution") or {}
                    tok = sol.get("gRecaptchaResponse") or sol.get("token")
                    ua  = sol.get("userAgent")
                    if not tok:
                        emit_log("⚠️ v2 ready but no gRecaptchaResponse", "error"); return None
                    with _token_cache_lock:
                        _token_cache.update({"token": tok, "user_agent": ua, "fetched_at": time.time()})
                    emit_log(f"✅ v2 solved in {int(time.time()-start)}s (len={len(tok)}) — cached", "success")
                    return {"token": tok, "userAgent": ua}
                if status in ("failed", "expired"):
                    emit_log(f"❌ v2 task {status}: {rd.get('errorDescription') or rd.get('errorCode') or 'unknown'}", "error")
                    return None
                if rd.get("errorId", 1) != 0:
                    emit_log(f"⚠️ getResult err: {rd.get('errorDescription') or rd.get('errorCode')}", "warning")
            except Exception as e:
                emit_log(f"⚠️ v2 poll error: {str(e)[:100]}", "warning")

        emit_log(f"❌ v2 timeout ({SOLVERCF_TIMEOUT}s)", "error")
        return None


def solve_recaptcha(page_action: str = None, force_fresh: bool = False) -> Optional[Dict]:
    return solve_solvercf(page_action=page_action, force_fresh=force_fresh)


# ============================
# FIREBASE helpers
# ============================
def _fb_get(url: str, timeout: int = 12):
    with _firebase_sem:
        r = requests.get(url, timeout=timeout, headers={"User-Agent": UA})
        r.raise_for_status()
        return r.json()


def _fb_delete(url: str, timeout: int = 8) -> bool:
    try:
        with _firebase_sem:
            r = requests.delete(url, timeout=timeout, headers={"User-Agent": UA})
            return r.status_code in (200, 204)
    except Exception:
        return False


def normalize_fb_url(raw: str) -> Optional[str]:
    u = (raw or "").strip()
    if not u: return None
    if not u.startswith(("http://", "https://")): u = "https://" + u
    if not u.endswith("/"): u += "/"
    if "firebaseio.com" not in u and "firebasedatabase.app" not in u: return None
    return u


# ============================
# PANEL FETCH
# ============================
def fetch_devices_from_panel(fb_url: str) -> List[Dict]:
    try:
        with _panel_fetch_sem:
            r = requests.get(fb_url + "clients.json", timeout=25, headers={"User-Agent": UA})
            r.raise_for_status()
            clients = r.json()
    except Exception as e:
        emit_log(f"Panel fetch failed ({fb_url[:40]}): {e}", "error")
        return []
    if not isinstance(clients, dict):
        return []

    online = [(cid, c) for cid, c in clients.items()
              if isinstance(c, dict) and c.get("status")]
    if not online:
        emit_log(f"Panel has 0 online clients ({fb_url[:40]})", "warning")
        return []

    emit_log(f"Found {len(online)} online devices — extracting phones…", "info")

    def _process(item):
        cid, c = item
        for k in ("phone", "mobile", "number", "phoneNumber", "msisdn",
                  "mob", "mobNo", "mobileNo", "phone_number", "mobile_no"):
            raw = c.get(k)
            if raw:
                digits = re.sub(r"\D", "", str(raw))
                if len(digits) >= 10:
                    return {"phone": digits[-10:], "client_id": cid}
        try:
            q = urllib.parse.quote('"$key"', safe='')
            with _panel_fetch_sem:
                r = requests.get(
                    f'{fb_url}messages/{cid}.json?orderBy={q}&limitToLast=1',
                    timeout=8, headers={"User-Agent": UA},
                )
            if r.status_code == 200:
                msgs = r.json()
                if isinstance(msgs, dict):
                    for v in msgs.values():
                        if not isinstance(v, dict):
                            continue
                        body = str(v.get("body") or v.get("message") or v.get("text") or "")
                        for pat in PHONE_PATTERNS:
                            m = pat.search(body)
                            if m:
                                ph = m.group(1) if m.groups() else m.group(0)
                                if re.fullmatch(r"[6-9]\d{9}", ph):
                                    return {"phone": ph, "client_id": cid}
        except Exception:
            pass
        return None

    result, seen = [], set()
    with ThreadPoolExecutor(max_workers=DEVICE_FETCH_THREADS) as ex:
        futures = [ex.submit(_process, item) for item in online]
        for f in as_completed(futures):
            try:
                r = f.result()
                if r and r["phone"] not in seen:
                    seen.add(r["phone"])
                    result.append(r)
            except Exception:
                pass
    emit_log(f"Extracted {len(result)} unique phone(s)", "success")
    return result


def prefetch_all_panels(force: bool = False):
    with state_lock:
        panels = list(state["panels"])
    emit_log("═" * 50, "info")
    seen_urls = set(); unique_panels = []; dup_count = 0
    for link in panels:
        fu = parse_panel_link(link)
        if not fu: continue
        if fu in seen_urls:
            dup_count += 1; continue
        seen_urls.add(fu); unique_panels.append(fu)
    if dup_count:
        emit_log(f"⚠️  {dup_count} duplicate panel(s) skipped", "warning")
    emit_log(f"🔍 PREFETCH: {len(unique_panels)} unique panel(s)", "info")
    for idx, firebase_url in enumerate(unique_panels, 1):
        with _panel_cache_lock:
            if not force and firebase_url in _panel_cache:
                emit_log(f"Panel #{idx}: cached ({len(_panel_cache[firebase_url])} dev) — skip", "info")
                continue
        devices = fetch_devices_from_panel(firebase_url)
        with _panel_cache_lock:
            _panel_cache[firebase_url] = devices
    total = sum(len(v) for v in _panel_cache.values())
    emit_log(f"🔍 PREFETCH DONE → {total} device(s) across {len(_panel_cache)} panel(s)", "success")
    emit_log("═" * 50, "info")


def get_cached_devices(firebase_url: str) -> List[Dict]:
    with _panel_cache_lock:
        return list(_panel_cache.get(firebase_url, []))


def clear_panel_cache():
    with _panel_cache_lock:
        _panel_cache.clear()


# ============================
# MESSAGE helpers
# ============================
def fetch_recent_messages(fb_url: str, client_id: str, n: int = 10) -> Dict:
    try:
        q = urllib.parse.quote('"$key"', safe='')
        url = f"{fb_url}messages/{client_id}.json?orderBy={q}&limitToLast={n}"
        data = _fb_get(url, timeout=12)
        if isinstance(data, dict):
            return data
    except Exception:
        pass
    try:
        data = _fb_get(f"{fb_url}messages/{client_id}.json", timeout=12)
        if not isinstance(data, dict):
            return {}
        if len(data) > n:
            keys = sorted(data.keys(), key=lambda k: (len(k), k))[-n:]
            return {k: data[k] for k in keys}
        return data
    except Exception:
        return {}


def get_newest_key(fb_url: str, client_id: str) -> str:
    try:
        msgs = fetch_recent_messages(fb_url, client_id, n=1)
        if isinstance(msgs, dict) and msgs:
            return max(msgs.keys(), key=lambda k: (len(k), k))
    except Exception:
        pass
    return ""


def delete_message(fb_url: str, client_id: str, msg_key: str) -> bool:
    return _fb_delete(f"{fb_url}messages/{client_id}/{msg_key}.json")


def _is_unomer(msg: dict) -> bool:
    sender = str(msg.get("sender") or msg.get("from") or "").lower()
    body = str(msg.get("body") or msg.get("message") or msg.get("text") or "").lower()
    return "unomer" in sender or "unomer" in body


def poll_for_otp(fb_url: str, client_id: str, baseline_key: str,
                 timeout: int = OTP_POLL_TIMEOUT, cancel_check=None):
    deadline = time.time() + timeout
    while time.time() < deadline:
        if cancel_check and cancel_check():
            return None
        try:
            msgs = fetch_recent_messages(fb_url, client_id, n=10)
            if isinstance(msgs, dict):
                for k in sorted(msgs.keys(), key=lambda x: (len(x), x), reverse=True):
                    if k <= baseline_key:
                        continue
                    v = msgs[k]
                    if not isinstance(v, dict): continue
                    if not _is_unomer(v): continue
                    body = str(v.get("body") or v.get("message") or v.get("text") or "")
                    m = OTP_PATTERN.search(body)
                    if m:
                        return (k, m.group(1), body)
        except Exception:
            pass
        time.sleep(OTP_POLL_INTERVAL)
    return None


def fetch_last_5_messages(fb_url: str, device_id: str) -> List[Dict]:
    if not fb_url or not device_id: return []
    try:
        if not fb_url.endswith("/"): fb_url += "/"
        msgs = _fb_get(f"{fb_url}messages/{device_id}.json", timeout=8)
        if not isinstance(msgs, dict): return []
        sorted_msgs = sorted(msgs.items(),
                             key=lambda x: (len(x[0]), x[0]), reverse=True)[:5]
        return [{"sender": m.get("sender", "Unknown"),
                 "text": m.get("body") or m.get("message") or m.get("text") or "",
                 "timestamp": k}
                for k, m in sorted_msgs if isinstance(m, dict)]
    except Exception as e:
        emit_log(f"Error fetching messages for {device_id}: {e}", "warning")
        return []


# ============================
# DUPLICATE NUMBERS
# ============================
_duplicate_numbers_lock = threading.Lock()


def load_duplicate_numbers() -> set:
    phones = set()
    if not os.path.exists(DUPLICATE_NUMBERS_TXT): return phones
    try:
        with open(DUPLICATE_NUMBERS_TXT, "r") as f:
            for line in f:
                p = line.strip().split("#")[0].strip()
                if p: phones.add(p)
    except Exception: pass
    return phones


def add_duplicate_number(phone: str, reason: str = ""):
    if not phone: return
    phone = str(phone).strip()
    with _duplicate_numbers_lock:
        if phone in load_duplicate_numbers(): return
        with open(DUPLICATE_NUMBERS_TXT, "a") as f:
            note = f"  # {reason}" if reason else ""
            f.write(f"{phone}{note}\n")
        emit_log(f"💾 Duplicate saved: {phone} ({reason or 'duplicate'})", "warning")


def is_duplicate_number(phone: str) -> bool:
    if not phone: return False
    with _duplicate_numbers_lock:
        return str(phone).strip() in load_duplicate_numbers()


def record_otp_fetch_fail(phone: str) -> int:
    if not phone: return 0
    phone = str(phone).strip()
    with _duplicate_numbers_lock:
        data = load_json(OTP_FAIL_COUNTS_JSON, {})
        if not isinstance(data, dict): data = {}
        count = int(data.get(phone, 0)) + 1
        data[phone] = count
        save_json(OTP_FAIL_COUNTS_JSON, data)
        return count


# ============================
# SAVED ACCOUNTS
# ============================
def load_saved_accounts():
    return load_json(SAVED_ACCOUNTS_JSON, {"accounts": []}).get("accounts", [])


def save_saved_accounts(accounts):
    save_json(SAVED_ACCOUNTS_JSON, {"accounts": accounts})


def append_account_log(phone, referral_code, extra=""):
    line = f"{datetime.now().isoformat()} | {phone} | {referral_code} | {extra}\n"
    with open(ACCOUNTS_LOG_TXT, "a") as f: f.write(line)


def upsert_saved_account(account):
    with accounts_lock:
        accounts = load_saved_accounts()
        found = False
        for i, a in enumerate(accounts):
            if a.get("phone") == account.get("phone"):
                accounts[i].update(account); found = True; break
        if not found: accounts.append(account)
        save_saved_accounts(accounts)
        append_account_log(account.get("phone", ""),
                          account.get("own_referral_code") or account.get("referral_code", ""),
                          account.get("firebase_url", "")[:60])


def delete_saved_account(phone):
    with accounts_lock:
        accounts = load_saved_accounts()
        accounts = [a for a in accounts if a.get("phone") != phone]
        save_saved_accounts(accounts)
        with open(ACCOUNTS_LOG_TXT, "w") as f:
            for a in accounts:
                f.write(f"{a.get('created_at','')} | {a.get('phone','')} | "
                       f"{a.get('own_referral_code') or a.get('referral_code','')} | "
                       f"{a.get('firebase_url','')[:60]}\n")


def load_session(mobile):
    return load_json(SESSIONS_FILE, {}).get(mobile)


def save_session(mobile, cookies, ref_code, extra=None):
    with session_file_lock:
        data = load_json(SESSIONS_FILE, {})
        data[mobile] = {"voyz_data": cookies.get("voyz_data"),
                       "PHPSESSID": cookies.get("PHPSESSID"),
                       "referral_code": ref_code}
        if extra: data[mobile].update(extra)
        save_json(SESSIONS_FILE, data)


# ============================
# PANEL LINK PARSER
# ============================
def parse_panel_link(link):
    if not link: return None
    link = link.strip()
    if link.startswith("https://") and ("firebaseio.com" in link or "firebasedatabase.app" in link):
        if not link.endswith("/"): link += "/"
        return link
    parsed = urllib.parse.urlparse(link)
    qs = urllib.parse.parse_qs(parsed.query)
    if "s" not in qs: return None
    s_param = qs["s"][0] + "=" * ((4 - len(qs["s"][0]) % 4) % 4)
    try:
        decoded = base64.b64decode(s_param).decode("utf-8").split("|")[0].strip()
        if not decoded.endswith("/"): decoded += "/"
        return decoded
    except Exception:
        return None


# ============================
# VOYZ referral
# ============================
def extract_own_referral_code(session) -> Optional[str]:
    try:
        for base in ("https://www.voyz.store", "https://voyz.store"):
            try:
                r = session.get(f"{base}/challenges.php", timeout=10)
            except Exception:
                continue
            if r.status_code != 200: continue
            m = re.search(r'id=["\']referralUrlInput["\'][^>]*value=["\'][^"\']*r=([A-Za-z0-9]+)', r.text)
            if m:
                emit_log(f"Own referral: {m.group(1)}", "success")
                return m.group(1)
            m2 = re.search(r'utm=referral&(?:amp;)?r=([A-Za-z0-9]+)', r.text)
            if m2:
                emit_log(f"Own referral: {m2.group(1)}", "success")
                return m2.group(1)
    except Exception as e:
        emit_log(f"Referral extract error: {e}", "warning")
    return None


def _new_reg_session(ref_code, user_agent=None):
    session = create_retry_session()
    session.headers.update({
        "User-Agent": user_agent or UA, "Accept": "application/json",
        "Origin": "https://www.voyz.store",
        "Referer": "https://www.voyz.store/login.php",
        "Connection": "close",
    })
    try:
        session.get(f"https://www.voyz.store/index.php?utm=referral&r={ref_code}", timeout=10)
    except Exception:
        pass
    return session


# ============================
# SIGNUP + OTP
# ============================
def send_signup_otp(mobile, ref_code):
    url = "https://www.voyz.store/APIS/do_signup.php"

    def _post(session, token):
        try:
            resp = session.post(url, json={
                "action": "send_otp", "mobile_no": mobile,
                "referral_code": ref_code, "recaptcha_response": token,
            }, timeout=15)
        except Exception as e:
            return None, f"OTP API error: {e}"
        if resp.status_code != 200:
            return None, f"HTTP {resp.status_code}"
        try:
            data = resp.json()
        except Exception:
            return None, "bad JSON"
        if data.get("error_type") == "user_exists":
            return None, "DUPLICATE"
        if "captcha" in str(data).lower():
            return None, "CAPTCHA_FAIL"
        if data.get("success") is False and data.get("error_type"):
            return None, data.get("message") or data.get("error_type")
        return session, None

    sol = solve_recaptcha(page_action=VOYZ_PAGE_ACTION_REGISTER)
    if not sol: return None, "CAPTCHA_SOLVE_FAIL"

    session = _new_reg_session(ref_code, user_agent=sol.get("userAgent"))
    attempt = 0
    captcha_refresh_count = 0

    while attempt < OTP_RATE_LIMIT_MAX_ATTEMPTS:
        if _target_reached():
            return None, "TARGET_REACHED"

        attempt += 1
        _stagger_otp_send()
        result = _post(session, sol["token"])
        err = result[1]

        if err is None:
            if attempt > 1:
                emit_log(f"✅ {mobile}: OTP sent after {attempt} attempt(s)", "success")
            return result[0], None

        err_low = str(err).lower()

        if "too many" in err_low or "rate limit" in err_low or "try again" in err_low:
            wait = random.uniform(*OTP_RATE_LIMIT_BACKOFF)
            emit_log(
                f"⏳ {mobile}: rate-limited (attempt {attempt}/{OTP_RATE_LIMIT_MAX_ATTEMPTS}) "
                f"— retry in {wait:.1f}s",
                "warning",
            )
            time.sleep(wait)
            continue

        if err == "CAPTCHA_FAIL":
            if captcha_refresh_count >= 2:
                emit_log(f"❌ {mobile}: captcha still failing after 2 refreshes", "error")
                return None, "CAPTCHA_FAIL"
            captcha_refresh_count += 1
            _mark_token_rejected(sol["token"])
            emit_log(
                f"⚠️ {mobile}: Voyz rejected token — refreshing "
                f"({captcha_refresh_count}/2)",
                "warning",
            )
            fresh = solve_recaptcha(page_action=VOYZ_PAGE_ACTION_REGISTER)
            if not fresh:
                return None, "CAPTCHA_FAIL"
            sol = fresh
            session = _new_reg_session(ref_code, user_agent=fresh.get("userAgent"))
            continue

        if err == "DUPLICATE":
            return None, "DUPLICATE"

        return None, err

    emit_log(
        f"❌ {mobile}: rate-limit retries exhausted ({OTP_RATE_LIMIT_MAX_ATTEMPTS} tries)",
        "error",
    )
    return None, "RATE_LIMIT_EXHAUSTED"


def complete_registration(session, mobile, otp, ref_code, client_id, firebase_url):
    try:
        r = session.post("https://www.voyz.store/APIS/do_verify_otp.php", json={"otp": otp}, timeout=15)
        if r.status_code != 200 or not r.json().get("success"):
            return None, "OTP_VERIFY_FAIL"

        r = session.post("https://www.voyz.store/APIS/do_set_password.php",
                         json={"password": PASSWORD, "confirm_password": PASSWORD}, timeout=15)
        if r.status_code != 200 or not r.json().get("success"):
            return None, "PASSWORD_FAIL"

        cookies = session.cookies.get_dict()
        save_session(mobile, cookies, ref_code)
        session.headers.update({
            "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
            "Referer": "https://www.voyz.store/surveys.php",
        })
        own_ref = extract_own_referral_code(session)
        return session, "SUCCESS", cookies, own_ref
    except Exception as e:
        return None, str(e)


def _target_reached():
    with state_lock:
        return state["stop_event"].is_set() or state["success_count"] >= state["target"]


def send_and_fetch_otp(dev, firebase_url, ref_code):
    mobile = dev["phone"]
    client_id = dev["client_id"]

    if _target_reached(): return None
    if is_duplicate_number(mobile):
        emit_log(f"Skip {mobile}: duplicate (in duplicate_numbers.txt)", "warning")
        return None
    if _target_reached(): return None

    baseline = get_newest_key(firebase_url, client_id)

    emit_log(f"Sending OTP → {mobile}", "info")
    session, err = send_signup_otp(mobile, ref_code)
    if session is None:
        if err == "TARGET_REACHED":
            return None
        if err == "RATE_LIMIT_EXHAUSTED":
            emit_log(f"OTP send exhausted {mobile}", "error")
            with state_lock:
                state["failed_count"] += 1; state["processed"] += 1
            emit_status()
            return None

        emit_log(f"OTP send failed {mobile}: {err}", "error")
        if err == "DUPLICATE":
            add_duplicate_number(mobile, reason="user_exists")
        with state_lock:
            state["failed_count"] += 1; state["processed"] += 1
        emit_status()
        return None

    got = poll_for_otp(firebase_url, client_id, baseline,
                       timeout=OTP_POLL_TIMEOUT, cancel_check=_target_reached)
    if not got:
        if _target_reached(): return None
        count = record_otp_fetch_fail(mobile)
        emit_log(f"OTP timeout {mobile} (fail #{count})", "error")
        with state_lock:
            state["failed_count"] += 1; state["no_otp_count"] += 1; state["processed"] += 1
        emit_status()
        return None

    msg_key, otp, _ = got
    emit_log(f"OTP for {mobile}: {otp}", "success")

    return {
        "mobile": mobile, "client_id": client_id,
        "firebase_url": firebase_url,
        "session": session, "otp": otp, "ref_code": ref_code,
    }


# ============================
# SURVEY
# ============================
def extract_q_from_html(html_text):
    start = html_text.find("postedDataWithSurveyId")
    if start == -1: return None
    colon = html_text.find(":", start)
    if colon == -1: colon = html_text.find("=", start)
    if colon == -1: return None
    q1 = html_text.find("'", colon)
    if q1 == -1: q1 = html_text.find('"', colon)
    if q1 == -1: return None
    q2 = html_text.find("'", q1 + 1)
    if q2 == -1: q2 = html_text.find('"', q1 + 1)
    if q2 == -1: return None
    return html_text[q1 + 1:q2]


def extract_voyz_and_flow(html_content):
    voyz = flow = None
    m = re.search(r'"voyz_mobile_no"\s*:\s*"([^"]+)"', html_content)
    if m: voyz = m.group(1)
    m = re.search(r'"flowId"\s*:\s*(\d+)', html_content)
    if m: flow = int(m.group(1))
    if not voyz or not flow:
        dj = re.search(r'<div id="domJson"[^>]*>(.*?)</div>', html_content, re.DOTALL)
        if dj:
            try:
                txt = html_mod.unescape(dj.group(1))
                txt = re.sub(r"<[^>]+>", "", txt)
                obj = json.loads(txt)
                ud = obj.get("userDetails", {})
                ep = ud.get("extra_param", {})
                if not voyz: voyz = ep.get("voyz_mobile_no")
                if not flow: flow = ud.get("flowId")
            except Exception:
                pass
    return voyz, flow


def do_survey(session, mobile=None, ref_code=None):
    session.get("https://voyz.store/surveys.php", timeout=15)
    resp = session.get(f"https://voyz.store/survey_viewer.php?survey_id={SURVEY_ID}",
                       headers={"Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
                                "Referer": "https://voyz.store/surveys.php",
                                "Sec-Fetch-Dest": "iframe", "Sec-Fetch-Mode": "navigate",
                                "Sec-Fetch-Site": "same-origin", "Connection": "close"}, timeout=15)
    if resp.status_code != 200: return False
    enc_q = extract_q_from_html(resp.text)
    if not enc_q: return False

    cs = create_retry_session()
    cs.headers.update({
        "User-Agent": UA, "Content-Type": "application/x-www-form-urlencoded; charset=UTF-8",
        "Accept": "application/json, text/javascript, */*; q=0.01",
        "Origin": "https://voyz.store", "Referer": "https://voyz.store/",
        "X-Requested-With": "XMLHttpRequest",
        "Sec-Fetch-Site": "cross-site", "Sec-Fetch-Mode": "cors", "Connection": "close",
    })
    cs.post("https://sms.unomer.com/apis/survey_flow_actions/api.php", data={"q": enc_q}, timeout=15)
    resp = cs.post("https://sms.unomer.com/surveys/survey-details", data={
        "q": enc_q, "surveyId": SURVEY_ID, "isPreview": "",
        "isRedirect": "false", "isDesktopSurvey": "1",
    }, timeout=15)
    if "UNOMER_APP" in resp.cookies:
        cs.cookies.set("UNOMER_APP", resp.cookies["UNOMER_APP"])
    if resp.status_code != 200: return False
    try: jd = json.loads(resp.text)
    except Exception: return False
    html_content = jd.get("html", "")
    if not html_content: return False

    request_token_id = jd.get("moreOptions", {}).get("responseToken")
    if not request_token_id: return False
    device_id = jd.get("user_data", {}).get("device_id")
    if not device_id: return False
    city = jd.get("user_data", {}).get("city", "Delhi")
    voyz_mobile, flow_id = extract_voyz_and_flow(html_content)
    if not voyz_mobile or not flow_id: return False

    imp = re.search(r'id=["\']impressionData["\']\s+value=["\']([^"\']+)["\']', html_content)
    if not imp: return False
    cs.post("https://sms.unomer.com/apis/api.php", data={"q": imp.group(1)}, timeout=15)

    sequence = [1, 2, 3, 4, 5, 7, 9, 8]
    ans_map = {
        1: {"response": "1", "opts": "0", "text": "Next", "theme": 19},
        2: {"response": "2", "opts": "0,1", "text": "Female", "theme": 100},
        3: {"response": "2", "opts": "0,1,2,3,4,5", "text": "18-24 years", "theme": 100},
        4: {"response": "1", "opts": "0,1", "text": "Yes", "theme": 100},
        5: {"response": "1", "opts": "0,1,2,3,4,5", "text": "Graduate/Post-Graduate: Professional", "theme": 131},
        7: {"response": "1", "opts": "0,1,2,3,4,5", "text": "Two-Wheeler", "theme": 101},
        9: {"response": "1", "opts": "0", "text": "telegram", "theme": 27},
        8: {"response": "1", "opts": "0", "text": "Submit", "theme": 19},
    }
    sess_id = f"SPT_{int(time.time()*1000)}_{''.join(random.choices('abcdefghijklmnopqrstuvwxyz', k=6))}"
    start_ts = time.time(); ts_start = int(start_ts * 1000); q_ts = {}; q_count = 0

    for q_no in sequence:
        q_count += 1
        think = random.uniform(2.5, 4.5) if q_no == 9 else \
                random.uniform(0.4, 0.8) if q_no == 8 else \
                random.uniform(1.0, 2.0) if q_no == 1 else random.uniform(0.6, 1.5)
        q_ts[q_no] = int(think * 1000)
        time.sleep(think)
        el = int(time.time() - start_ts)
        tstr = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%S.%f")[:-3] + "Z"
        try:
            cs.post("https://sms.unomer.com/apis/question_log.php",
                    data={"device_id": device_id, "survey_id": SURVEY_ID,
                          "question_no": str(q_no), "city": city}, timeout=15)
        except Exception: pass
        try:
            session.post("https://www.voyz.store/APIS/do_log_survey_progress.php", json={
                "survey_id": SURVEY_ID, "session_id": sess_id, "event": "question_progress",
                "questions_answered": q_count, "elapsed_seconds": el, "timestamp": tstr,
            }, timeout=15)
        except Exception: pass

    prof = {1:"",2:"UNOMER_GENDER",3:"UNOMER_AGE",4:"",5:"UNOMER_EDUCATION",
            7:"UNOMER_DURABLES",9:"",8:"UNOMER_THANK"}
    qlist = []; acc = 0
    for q_no in sequence:
        acc += q_ts[q_no]; ts = ts_start + acc; a = ans_map[q_no]
        qlist.append({
            "response": a["response"], "optsSequence": a["opts"], "qTime": q_ts[q_no],
            "txtResponse": a["text"], "themeNo": a["theme"], "timeStamp": ts,
            "previousQuestion": "NOT_SET", "imgResponse": "-", "ignoreThis": f"{ts}_false",
            "questionType": "NORMAL_QUESTION", "qNo": q_no,
            "pipingQuestionKeyword": "NOT_SET",
            "pass_on_data": {"profileData": 1 if q_no in [2,3,5,7,8] else 0,
                             "profileFieldName": prof.get(q_no, "")},
        })
    qlist.sort(key=lambda x: x["qNo"])
    actual_ref = ref_code or state["referral_code"]
    pending = [{"surveyID": SURVEY_ID, "app_location": "Default",
                "requestTokenId": request_token_id, "rewardValue": 0, "rewardCurrency": "",
                "surveyCadre": "A", "questions": qlist, "userDisqualified": "false",
                "surveyTime": sum(q_ts.values()), "userQuit": "false",
                "lastQNo": 8, "questionSequence": sequence}]

    res_str = {
        "publisher_key": "fzwT6LXmQBgzHH9+qJP1dA==", "app_id": "5SoYjuNd2Fvs1ERZJlnzIciQ9mCVBG",
        "device_id": device_id, "end_user_email": "NOT_SET", "country_code": "IN",
        "device_type": "Linux", "os_type": "Google Chrome", "language": "NOT_SET",
        "age": "NOT_SET", "gender": "NOT_SET", "age_by_app": "NOT_SET", "gender_by_app": "NOT_SET",
        "street": "NOT_SET", "state": "National Capital Territory of Delhi", "city": city,
        "end_user_name": device_id, "app_params": "NOT_SET", "model": "NOT_SET",
        "network_type": "NOT_SET", "lat": "NOT_SET", "long": "NOT_SET",
        "email_by_app": "NOT_SET", "os_version": "114.0.5735.198#5.15.0", "pincode": "NOT_SET",
        "manufacturer": "NOT_SET", "network_carrier": "NOT_SET", "geographics": "NO",
        "last_displayed_survey_id": "NOT_SET", "backfill_by_app": "NOT_SET",
        "survey_test_code": "", "user_counter": "1", "cadre_by_app": "NOT_SET",
        "ignore_survey_ids": "", "list_of_apps_installed": "NOT_SET",
        "list_of_apps_installed_by_user": "NOT_SET", "app_package": "com.unomer.voyz",
        "sdk_version": "15.4", "app_location": "Default", "google_ad_id": device_id,
        "cellMNC": "NOT_SET", "cellLocationCode": "NOT_SET", "cellMCC": "NOT_SET",
        "cellID": "NOT_SET", "marital": "NOT_SET", "vehicle": "NOT_SET",
        "qualification": "NOT_SET", "device_resolution": "NOT_SET", "device_version": "NOT_SET",
        "extra_param": {"distribution_channel": "SMS", "os_type": "Google Chrome",
                        "os_version": "114.0.5735.198#5.15.0", "device_type": "Linux",
                        "voyz_mobile_no": voyz_mobile, "voyz_survey_amount": "0",
                        "source": "NOT_SET", "refferal_code": actual_ref,
                        "campaign_id": "", "campaign_type": "",
                        "serverExtraParam": {"extraCallFlagToMeasureFetchResponseTime": "0"}},
        "flowId": flow_id, "web_survey": 1, "purpose": "upload-survey-response",
        "pending_survey_string": pending,
    }
    cs.post("https://sms.unomer.com/apis/api-web-survey-upload.php",
            data={"resStr": json.dumps(res_str)}, timeout=20)
    try:
        session.post("https://voyz.store/APIS/do_log_analytics.php",
                     json={"event_type": "session_end",
                           "event_data": {"duration_seconds": int(time.time() - start_ts)}}, timeout=10)
    except Exception: pass
    time.sleep(1)
    resp = session.get("https://voyz.store/transactions.php", timeout=15)
    wm = re.search(r"Wallet Balance.*?₹(\d+)", resp.text)
    if wm:
        bal = int(wm.group(1))
        emit_log(f"Wallet for {mobile}: ₹{bal}", "success")
        return bal > 0
    return False


# ============================
# WITHDRAW
# ============================
def login_with_password(mobile: str, password: str = PASSWORD):
    BASE = "https://www.voyz.store"
    sol = solve_recaptcha(page_action=VOYZ_PAGE_ACTION_LOGIN)
    if not sol: return None, "Login captcha failed"

    session = create_retry_session()
    session.headers.update({
        "User-Agent": sol.get("userAgent") or UA,
        "Content-Type": "application/json", "Accept": "application/json",
        "Origin": BASE, "Referer": f"{BASE}/login.php",
    })
    try:
        session.get(f"{BASE}/login.php", timeout=12)
        r = session.post(f"{BASE}/APIS/do_login.php",
                         json={"mobile_no": mobile, "recaptcha_response": sol["token"]}, timeout=15)
        data = r.json() if r.status_code == 200 else {}
        if not data.get("success") and not data.get("requires_password"):
            if "captcha" in str(data).lower(): _mark_token_rejected(sol["token"])
            return None, data.get("message") or "Login failed"

        r2 = session.post(f"{BASE}/APIS/do_verify_password.php",
                          json={"mobile_no": mobile, "password": password}, timeout=15)
        data2 = r2.json() if r2.status_code == 200 else {}
        if not data2.get("success"):
            return None, data2.get("message") or "Password failed"

        session.headers["Accept"] = "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8"
        session.headers["Referer"] = f"{BASE}/login.php"
        session.get(f"{BASE}/surveys.php", timeout=15)
        cookies = session.cookies.get_dict()
        if not cookies.get("voyz_data") and not cookies.get("PHPSESSID"):
            return None, "No session cookies"
        session.headers["Accept"] = "*/*"; session.headers["Content-Type"] = "application/json"
        session.headers["Origin"] = BASE; session.headers["Referer"] = f"{BASE}/surveys.php"
        return session, cookies
    except Exception as e:
        return None, str(e)


def session_looks_invalid(session) -> bool:
    try:
        prev = session.headers.get("Accept")
        session.headers["Accept"] = "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8"
        resp = session.get("https://www.voyz.store/surveys.php", timeout=12)
        if prev: session.headers["Accept"] = prev
        text = (resp.text or "").lower()
        if resp.status_code in (401, 403): return True
        if "login.php" in str(getattr(resp, "url", "")).lower(): return True
        if "wallet balance" in text or "your rewards" in text or "surveys - voyz" in text: return False
        if "login" in text and ("password" in text or "otp" in text): return True
        return False
    except Exception:
        return True


def do_withdraw(phone, amount=WITHDRAW_AMOUNT):
    BASE = "https://www.voyz.store"
    accounts = load_saved_accounts()
    account = next((a for a in accounts if a.get("phone") == phone), None)
    if not account: return False, "Account not found"

    fb_url = account.get("firebase_url"); client_id = account.get("client_id")
    if not fb_url or not client_id: return False, "Missing fb_url/client_id"

    def persist(cookies):
        save_session(phone, cookies, account.get("referral_code") or state["referral_code"])
        with accounts_lock:
            accs = load_saved_accounts()
            for a in accs:
                if a.get("phone") == phone:
                    a["voyz_data"] = cookies.get("voyz_data"); a["PHPSESSID"] = cookies.get("PHPSESSID")
            save_saved_accounts(accs)

    def build(vd, ps):
        s = create_retry_session()
        if vd: s.cookies.set("voyz_data", vd)
        if ps: s.cookies.set("PHPSESSID", ps)
        s.headers.update({"User-Agent": UA, "Content-Type": "application/json",
                          "Accept": "*/*", "Origin": BASE, "Referer": f"{BASE}/surveys.php"})
        return s

    def ensure_login():
        login_sess, res = login_with_password(phone, PASSWORD)
        if login_sess is None: return None, f"Re-login failed: {res}"
        persist(res)
        return login_sess, None

    session = build(account.get("voyz_data"), account.get("PHPSESSID"))
    need = not account.get("voyz_data") or not account.get("PHPSESSID")
    if not need: need = session_looks_invalid(session)
    if need:
        session, err = ensure_login()
        if err: return False, err

    def send_otp(sess):
        sess.post(f"{BASE}/APIS/do_log_analytics.php", json={"event_type": "withdraw_modal_opened"}, timeout=15)
        sess.post(f"{BASE}/APIS/do_log_analytics.php",
                  json={"event_type": "withdraw_amount_selected", "event_data": {"amount": amount}}, timeout=15)
        return sess.post(f"{BASE}/APIS/do_send_withdrawal_otp.php", json={"amount": amount}, timeout=15)

    try:
        baseline = get_newest_key(fb_url, client_id)
        r = send_otp(session)
        bad = (r.status_code in (401, 403) or any(x in (r.text or "").lower()
               for x in ("session invalid","user session","expired","unauthorized","not logged")))
        if bad:
            session, err = ensure_login()
            if err: return False, err
            r = send_otp(session)
            if r.status_code >= 400: return False, r.text[:300]

        got = poll_for_otp(fb_url, client_id, baseline, timeout=40)
        if not got: return False, "Withdrawal OTP timeout"
        msg_key, otp, _ = got
        emit_log(f"Withdraw OTP for {phone}: {otp}", "success")

        r = session.post(f"{BASE}/APIS/do_verify_withdrawal_otp.php",
                         json={"otp": otp, "amount": amount}, timeout=15)
        try:
            data = r.json()
            if data.get("success"): return True, "Withdrawal successful"
            return False, data.get("message") or "Payment failed"
        except Exception:
            return False, r.text[:200]
    except Exception as e:
        return False, str(e)


# ============================
# SURVEY WORKERS
# ============================
def run_survey_for_mobile(mobile):
    saved = load_session(mobile)
    if not saved:
        acc = next((a for a in load_saved_accounts() if a.get("phone") == mobile), None)
        if not acc:
            emit_log(f"Session not found for {mobile}", "error"); return
        saved = {"voyz_data": acc.get("voyz_data"), "PHPSESSID": acc.get("PHPSESSID"),
                 "referral_code": acc.get("referral_code")}
    session = create_retry_session()
    session.cookies.set("voyz_data", saved["voyz_data"])
    session.cookies.set("PHPSESSID", saved["PHPSESSID"])
    try:
        resp = session.get("https://voyz.store/surveys.php", timeout=15)
        if "Surveys - Voyz" not in resp.text and "survey" not in resp.text.lower():
            emit_log(f"Session expired for {mobile}", "error"); return
        ok = do_survey(session, mobile, saved.get("referral_code", state["referral_code"]))
        emit_log(f"Survey {'OK' if ok else 'FAILED'} for {mobile}", "success" if ok else "warning")
    except Exception as e:
        emit_log(f"Survey error {mobile}: {e}", "error")


def survey_worker():
    while True:
        try:
            mobile = survey_queue.get(timeout=1)
        except Exception:
            if state["stop_event"].is_set() and survey_queue.empty(): break
            continue
        with state_lock: state["active_workers"] += 1
        emit_status()
        time.sleep(random.uniform(2, 4))
        run_survey_for_mobile(mobile)
        survey_queue.task_done()
        with state_lock: state["active_workers"] = max(0, state["active_workers"] - 1)
        emit_status()


# ============================
# MAIN AUTOMATION
# ============================
def run_automation(mode="run"):
    state["stop_event"].clear()
    with state_lock:
        state["running"] = True; state["mode"] = mode
        state["success_count"] = 0; state["failed_count"] = 0
        state["no_otp_count"] = 0; state["processed"] = 0; state["numbers_found"] = []
    while not survey_queue.empty():
        try: survey_queue.get_nowait(); survey_queue.task_done()
        except Exception: break

    target = state["target"]
    ref_code = state["referral_code"]
    panels = list(state["panels"])

    emit_log(f"Started mode={mode} target={target} ref={ref_code} (batch={BATCH_SIZE})", "info")
    emit_log(f"🔍 {len(panels)} panel(s) queued — lazy fetch + {BATCH_SIZE}/batch", "info")
    emit_log(f"⏱  OTP stagger: min {OTP_MIN_SEND_GAP}s + jitter {OTP_JITTER_MIN}-{OTP_JITTER_MAX}s", "info")
    emit_log(f"🔁 Rate-limit retry: {OTP_RATE_LIMIT_MAX_ATTEMPTS} tries, "
             f"{OTP_RATE_LIMIT_BACKOFF[0]}-{OTP_RATE_LIMIT_BACKOFF[1]}s delay", "info")

    success_count = 0
    seen_fb_urls = set()

    for panel_idx, link in enumerate(panels, 1):
        if state["stop_event"].is_set() or success_count >= target:
            break

        with state_lock: state["current_panel_idx"] = panel_idx - 1
        emit_status()

        firebase_url = parse_panel_link(link)
        if not firebase_url:
            emit_log(f"Panel #{panel_idx}: invalid URL", "error"); continue
        if firebase_url in seen_fb_urls:
            emit_log(f"Panel #{panel_idx}: duplicate URL — skip", "info"); continue
        seen_fb_urls.add(firebase_url)

        devices = get_cached_devices(firebase_url)
        if devices:
            emit_log(f"Panel #{panel_idx}: cached ({len(devices)} devices)", "info")
        else:
            emit_log(f"Panel #{panel_idx}: fetching devices…", "info")
            devices = fetch_devices_from_panel(firebase_url)
            with _panel_cache_lock: _panel_cache[firebase_url] = devices
        if not devices:
            emit_log(f"Panel #{panel_idx}: 0 devices — next", "warning"); continue

        dups = load_duplicate_numbers()
        seen = set(); unique = []; skipped = 0
        for d in devices:
            p = d.get("phone")
            if not p or p in seen: continue
            seen.add(p)
            if p in dups: skipped += 1; continue
            unique.append(d)
        if skipped:
            emit_log(f"Panel #{panel_idx}: {skipped} duplicate(s) skipped", "warning")
        if not unique:
            emit_log(f"Panel #{panel_idx}: 0 usable — next", "warning"); continue

        emit_log(f"Panel #{panel_idx}: {len(unique)} usable — need {target - success_count}", "info")

        for batch_start in range(0, len(unique), BATCH_SIZE):
            if state["stop_event"].is_set() or success_count >= target:
                break

            batch = unique[batch_start:batch_start + BATCH_SIZE]
            batch_num = batch_start // BATCH_SIZE + 1
            total_batches = (len(unique) + BATCH_SIZE - 1) // BATCH_SIZE
            emit_log(
                f"Panel #{panel_idx} batch {batch_num}/{total_batches}: "
                f"{len(batch)} numbers (need {target - success_count})",
                "info",
            )

            executor = ThreadPoolExecutor(max_workers=min(15, len(batch)))
            futures = {executor.submit(send_and_fetch_otp, d, firebase_url, ref_code): d
                       for d in batch}
            pending = set(futures.keys())

            try:
                for f in as_completed(futures):
                    pending.discard(f)

                    if success_count >= target or state["stop_event"].is_set():
                        for pf in pending: pf.cancel()
                        emit_log(
                            f"Panel #{panel_idx} batch {batch_num}: "
                            f"🎯 target reached — cancelling {len(pending)} pending",
                            "success",
                        )
                        break

                    item = f.result()
                    if not item: continue

                    mobile = item["mobile"]
                    result = complete_registration(
                        item["session"], mobile, item["otp"],
                        item["ref_code"], item["client_id"], item["firebase_url"],
                    )
                    if result[0] is None:
                        emit_log(f"Submit failed {mobile}: {result[1]}", "error")
                        with state_lock:
                            state["failed_count"] += 1
                            state["processed"] += 1
                        emit_status()
                        continue

                    session, status, cookies, own_ref = result
                    emit_log(f"✅ Registered {mobile} own_ref={own_ref or 'N/A'}", "success")
                    upsert_saved_account({
                        "phone": mobile, "client_id": item["client_id"],
                        "firebase_url": item["firebase_url"],
                        "referral_code": ref_code, "own_referral_code": own_ref or "",
                        "voyz_data": cookies.get("voyz_data"),
                        "PHPSESSID": cookies.get("PHPSESSID"),
                        "can_withdraw": False,
                        "created_at": datetime.now().isoformat(),
                    })
                    with state_lock:
                        state["success_count"] += 1
                        state["processed"] += 1
                        state["recent_accounts"].append({
                            "phone": mobile, "status": "SUCCESS",
                            "time": datetime.now().strftime("%H:%M:%S"),
                            "ref": own_ref or ref_code,
                        })
                        state["numbers_found"].append(mobile)
                    emit_status()
                    success_count += 1
                    survey_queue.put(mobile)
                    emit_log(f"Queued survey for {mobile} ({success_count}/{target})", "info")

                    if success_count >= target:
                        for pf in pending: pf.cancel()
                        emit_log(
                            f"Panel #{panel_idx} batch {batch_num}: "
                            f"🎯 target hit — cancelling {len(pending)} pending",
                            "success",
                        )
                        state["stop_event"].set()
                        break
            finally:
                executor.shutdown(wait=False, cancel_futures=True)

            if success_count >= target or state["stop_event"].is_set():
                break

        if success_count >= target:
            break

    if not survey_queue.empty():
        emit_log(f"Registrations done ({success_count}/{target}). Starting surveys…", "success")
        
        # --- NAYA CHANGE: Render ke liye socketio background task ---
        workers = [socketio.start_background_task(survey_worker) for _ in range(PARALLEL_SURVEYS)]
        
        survey_queue.join()
        state["stop_event"].set()
        
        with accounts_lock:
            accounts = load_saved_accounts(); enabled = []
            for a in accounts:
                own = (a.get("own_referral_code") or "").strip()
                if a.get("phone") in state["numbers_found"]:
                    a["can_withdraw"] = False; continue
                if own and own == ref_code:
                    a["can_withdraw"] = True; enabled.append(a.get("phone"))
            save_saved_accounts(accounts)
        socketio.emit("accounts_updated", {"accounts": load_saved_accounts()})
        if enabled:
            emit_log(f"Withdraw enabled: {', '.join(enabled)}", "success")

    with state_lock:
        state["running"] = False; state["mode"] = None
    emit_log(f"Done. Success: {success_count}/{target}", "success")
    emit_status()


# ============================
# API ROUTES
# ============================
@app.route("/")
def index(): return send_from_directory(STATIC_DIR, "index.html")


@app.route("/api/status")
def api_status():
    with state_lock:
        return jsonify({
            "running": state["running"], "mode": state["mode"],
            "target": state["target"], "referral_code": state["referral_code"],
            "anticaptcha_balance": None,
            "token_service_ok": state["solvercf_configured"],
            "solvercf_configured": state["solvercf_configured"],
            "success_count": state["success_count"], "failed_count": state["failed_count"],
            "no_otp_count": state["no_otp_count"], "processed": state["processed"],
            "queue_size": survey_queue.qsize(),
            "active_workers": state["active_workers"],
            "panels": state["panels"], "current_panel_idx": state["current_panel_idx"],
            "numbers_found": state["numbers_found"][-30:],
            "recent_accounts": state["recent_accounts"][-15:],
        })


@app.route("/api/config", methods=["POST"])
def api_config():
    data = request.json or {}
    with state_lock:
        if "target" in data: state["target"] = int(data["target"])
        if "referral_code" in data: state["referral_code"] = str(data["referral_code"]).strip()
    emit_status()
    return jsonify({"success": True, "target": state["target"], "referral_code": state["referral_code"]})


@app.route("/api/settings/key", methods=["GET"])
def api_get_key():
    s = load_settings()
    key = s.get("nextcaptcha_key") or os.environ.get("NEXTCAPTCHA_KEY") or DEFAULT_NEXTCAPTCHA_KEY
    masked = (key[:8] + "..." + key[-4:]) if len(key) > 12 else key
    source = "panel" if s.get("nextcaptcha_key") else ("env" if os.environ.get("NEXTCAPTCHA_KEY") else "default")
    return jsonify({"success": True, "key_masked": masked, "source": source})

@app.route("/api/settings/key", methods=["POST"])
def api_set_key():
    global SOLVERCF_KEY, NEXTCAPTCHA_KEY
    data = request.json or {}
    new_key = (data.get("key") or "").strip()
    if not new_key:
        return jsonify({"success": False, "error": "Key khali hai"})
    s = load_settings()
    s["nextcaptcha_key"] = new_key
    save_settings(s)
    SOLVERCF_KEY = new_key
    NEXTCAPTCHA_KEY = new_key
    state["solvercf_configured"] = True
    invalidate_token_cache()
    emit_log("🔑 NextCaptcha key panel se update ho gayi (ab yahi default)", "success")
    emit_status()
    return jsonify({"success": True})

@app.route("/api/settings/key/reset", methods=["POST"])
def api_reset_key():
    global SOLVERCF_KEY, NEXTCAPTCHA_KEY
    s = load_settings()
    s.pop("nextcaptcha_key", None)
    save_settings(s)
    fallback = (os.environ.get("NEXTCAPTCHA_KEY") or DEFAULT_NEXTCAPTCHA_KEY).strip()
    SOLVERCF_KEY = fallback
    NEXTCAPTCHA_KEY = fallback
    state["solvercf_configured"] = bool(fallback)
    invalidate_token_cache()
    emit_log("🔑 Key reset — ab script wali default key chal rahi hai", "warning")
    emit_status()
    return jsonify({"success": True})


@app.route("/api/solvercf/status")
@app.route("/api/token-service/status")
def api_solvercf_status():
    with _token_cache_lock:
        tok_present = bool(_token_cache["token"])
        age = int(time.time() - _token_cache["fetched_at"]) if _token_cache["token"] else 0
    return jsonify({
        "configured": bool(SOLVERCF_KEY), "online": bool(SOLVERCF_KEY),
        "solver": "NextCaptcha RecaptchaV2TaskProxyless",
        "provider": "nextcaptcha.com", "recaptcha_version": "v2",
        "v2_invisible": RECAPTCHA_V2_INVISIBLE, "v2_api_domain": RECAPTCHA_V2_API_DOMAIN,
        "sitekey": VOYZ_RECAPTCHA_SITEKEY, "page_url": VOYZ_PAGE_URL,
        "token_ttl": SOLVERCF_TOKEN_TTL,
        "cached_token_present": tok_present, "cached_token_age": age,
        "otp_send_min_gap": OTP_MIN_SEND_GAP,
        "otp_send_jitter": [OTP_JITTER_MIN, OTP_JITTER_MAX],
        "otp_rate_limit_max_attempts": OTP_RATE_LIMIT_MAX_ATTEMPTS,
        "otp_rate_limit_backoff": list(OTP_RATE_LIMIT_BACKOFF),
        "auto_start": False, "managed_process": False,
    })


@app.route("/api/solvercf/solve", methods=["POST"])
@app.route("/api/token-service/start", methods=["POST"])
@app.route("/api/token-service/restart", methods=["POST"])
def api_solvercf_solve():
    data = request.json or {}
    action = data.get("action") or VOYZ_PAGE_ACTION_REGISTER
    invalidate_token_cache()
    sol = solve_solvercf(page_action=action, force_fresh=True)
    return jsonify({"success": sol is not None,
                    "has_token": bool(sol and sol.get("token")),
                    "token_len": len(sol["token"]) if sol else 0})


@app.route("/api/token/cache-status")
def api_token_cache_status():
    with _token_cache_lock:
        tok = _token_cache["token"]
        age = int(time.time() - _token_cache["fetched_at"]) if tok else 0
    with _rejected_lock: rcount = len(_rejected_tokens)
    return jsonify({"has_token": bool(tok), "token_age": age,
                    "ttl": SOLVERCF_TOKEN_TTL,
                    "valid": bool(tok and age < SOLVERCF_TOKEN_TTL),
                    "rejected_count": rcount})


@app.route("/api/panels", methods=["GET"])
def api_panels_get():
    load_panels()
    with _panel_cache_lock:
        cached = {k: len(v) for k, v in _panel_cache.items()}
    return jsonify({"panels": state["panels"], "total": len(state["panels"]), "cache": cached})


@app.route("/api/panels/add", methods=["POST"])
def api_panels_add():
    data = request.json or {}
    urls = data.get("urls") or data.get("links") or []
    if isinstance(urls, str): urls = re.split(r"[\n,\s]+", urls)
    added = 0
    with state_lock:
        for u in urls:
            u = u.strip()
            if u and u not in state["panels"]:
                state["panels"].append(u); added += 1
    save_panels(); emit_status()
    return jsonify({"added": added, "total": len(state["panels"]), "panels": state["panels"]})


@app.route("/api/panels/clear", methods=["POST"])
def api_panels_clear():
    with state_lock: state["panels"] = []
    clear_panel_cache()
    save_panels(); emit_status()
    return jsonify({"success": True})


@app.route("/api/panels/delete", methods=["POST"])
def api_panels_delete():
    data = request.json or {}
    idx = data.get("index")
    with state_lock:
        if idx is not None and 0 <= idx < len(state["panels"]):
            state["panels"].pop(idx)
    save_panels(); emit_status()
    return jsonify({"success": True, "panels": state["panels"]})


@app.route("/api/panels/refresh", methods=["POST"])
def api_panels_refresh():
    clear_panel_cache()
    prefetch_all_panels(force=True)
    with _panel_cache_lock:
        cached = {k: len(v) for k, v in _panel_cache.items()}
    return jsonify({"success": True, "cache": cached})


@app.route("/api/start", methods=["POST"])
def api_start():
    if state["running"]:
        return jsonify({"success": False, "error": "Already running"})
    data = request.json or {}
    mode = data.get("mode", "run")
    if not state["panels"]: return jsonify({"success": False, "error": "Add panel links first"})
    if data.get("target"):
        with state_lock: state["target"] = int(data["target"])
    if data.get("referral_code"):
        with state_lock: state["referral_code"] = str(data["referral_code"]).strip()
    if not SOLVERCF_KEY: return jsonify({"success": False, "error": "NEXTCAPTCHA_KEY not configured"})
    
    # --- NAYA CHANGE: Render crash fix ---
    socketio.start_background_task(run_automation, mode)
    
    return jsonify({"success": True, "mode": mode})


@app.route("/api/stop", methods=["POST"])
def api_stop():
    state["stop_event"].set()
    emit_log("Stop signal sent", "warning")
    return jsonify({"success": True})


@app.route("/api/accounts", methods=["GET"])
def api_accounts(): return jsonify({"accounts": load_saved_accounts()})


@app.route("/api/accounts/use", methods=["POST"])
def api_accounts_use():
    data = request.json or {}
    phone = data.get("phone")
    acc = next((a for a in load_saved_accounts() if a.get("phone") == phone), None)
    if not acc: return jsonify({"success": False, "error": "Not found"})
    code = acc.get("own_referral_code") or acc.get("referral_code")
    if not code: return jsonify({"success": False, "error": "No referral"})
    with state_lock: state["referral_code"] = code
    emit_log(f"Active ref = {code} (from {phone})", "success")
    emit_status()
    return jsonify({"success": True, "referral_code": code})


@app.route("/api/accounts/delete", methods=["POST"])
def api_accounts_delete():
    data = request.json or {}
    phone = data.get("phone")
    if not phone: return jsonify({"success": False, "error": "phone required"})
    delete_saved_account(phone)
    socketio.emit("accounts_updated", {"accounts": load_saved_accounts()})
    return jsonify({"success": True})


@app.route("/api/accounts/withdraw", methods=["POST"])
def api_accounts_withdraw():
    data = request.json or {}
    phone = data.get("phone")
    amount = int(data.get("amount", WITHDRAW_AMOUNT))
    if not phone: return jsonify({"success": False, "error": "phone required"})

    def _run():
        emit_log(f"Withdraw start {phone} ₹{amount}", "info")
        ok, msg = do_withdraw(phone, amount)
        if ok:
            with accounts_lock:
                accounts = load_saved_accounts()
                for a in accounts:
                    if a.get("phone") == phone:
                        a["can_withdraw"] = False
                        a["last_withdraw"] = datetime.now().isoformat()
                save_saved_accounts(accounts)
            socketio.emit("accounts_updated", {"accounts": load_saved_accounts()})
        emit_log(f"Withdraw {'OK' if ok else 'FAIL'} {phone}: {msg}", "success" if ok else "error")
        socketio.emit("withdraw_result", {"phone": phone, "success": ok, "message": msg})

    # --- NAYA CHANGE: Render crash fix ---
    socketio.start_background_task(_run)
    
    return jsonify({"success": True, "message": "Started"})


@app.route("/api/accounts/messages", methods=["POST"])
def api_accounts_messages():
    data = request.json or {}
    phone = data.get("phone")
    if not phone: return jsonify({"success": False, "error": "phone required"})
    acc = next((a for a in load_saved_accounts() if a.get("phone") == phone), None)
    if not acc: return jsonify({"success": False, "error": "Not found"})
    fb_url = acc.get("firebase_url"); cid = acc.get("client_id")
    if not fb_url or not cid: return jsonify({"success": False, "error": "Missing fb_url/client_id"})
    msgs = fetch_last_5_messages(fb_url, cid)
    return jsonify({"success": True, "phone": phone, "client_id": cid,
                    "count": len(msgs), "messages": msgs})


@app.route("/api/accounts/messages/delete", methods=["POST"])
def api_accounts_messages_delete():
    data = request.json or {}
    phone = data.get("phone"); msg_key = data.get("msg_key")
    if not phone or not msg_key:
        return jsonify({"success": False, "error": "phone & msg_key required"})
    acc = next((a for a in load_saved_accounts() if a.get("phone") == phone), None)
    if not acc: return jsonify({"success": False, "error": "Not found"})
    fb_url = acc.get("firebase_url"); cid = acc.get("client_id")
    if not fb_url or not cid: return jsonify({"success": False, "error": "Missing fb_url/client_id"})
    ok = delete_message(fb_url, cid, msg_key)
    return jsonify({"success": bool(ok)})


@app.route("/api/accounts/messages/delete-all", methods=["POST"])
def api_accounts_messages_delete_all():
    data = request.json or {}
    phone = data.get("phone")
    if not phone: return jsonify({"success": False, "error": "phone required"})
    acc = next((a for a in load_saved_accounts() if a.get("phone") == phone), None)
    if not acc: return jsonify({"success": False, "error": "Not found"})
    fb_url = acc.get("firebase_url"); cid = acc.get("client_id")
    if not fb_url or not cid: return jsonify({"success": False, "error": "Missing fb_url/client_id"})
    try:
        msgs = _fb_get(f"{fb_url}messages/{cid}.json", timeout=10)
        if not isinstance(msgs, dict):
            return jsonify({"success": True, "deleted": 0})
        n = 0
        for k in list(msgs.keys()):
            if delete_message(fb_url, cid, k): n += 1
        return jsonify({"success": True, "deleted": n})
    except Exception as e:
        return jsonify({"success": False, "error": str(e)})


@app.route("/api/duplicates")
def api_duplicates():
    return jsonify({"duplicates": sorted(load_duplicate_numbers())})


@app.route("/api/duplicates/clear", methods=["POST"])
def api_duplicates_clear():
    with _duplicate_numbers_lock:
        if os.path.exists(DUPLICATE_NUMBERS_TXT):
            os.remove(DUPLICATE_NUMBERS_TXT)
    emit_log("Duplicate numbers file cleared", "info")
    return jsonify({"success": True})


@app.route("/api/fetch-devices", methods=["POST"])
def api_fetch_devices():
    data = request.json or {}
    link = data.get("link") or (state["panels"][state["current_panel_idx"]] if state["panels"] else None)
    if not link: return jsonify({"error": "No panel link"})
    firebase_url = parse_panel_link(link)
    if not firebase_url: return jsonify({"error": "Invalid link"})
    cached = get_cached_devices(firebase_url)
    if cached:
        return jsonify({"count": len(cached), "source": "cache",
                        "devices": [{"phone": d["phone"], "device": d["client_id"]} for d in cached],
                        "panel": firebase_url[:60]})
    devices = fetch_devices_from_panel(firebase_url)
    with _panel_cache_lock: _panel_cache[firebase_url] = devices
    return jsonify({"count": len(devices), "source": "fresh",
                    "devices": [{"phone": d["phone"], "device": d["client_id"]} for d in devices],
                    "panel": firebase_url[:60]})


@app.route("/api/logs")
def api_logs(): return jsonify({"logs": state["logs"][-100:]})


@socketio.on("connect")
def on_connect():
    emit_status()
    emit("accounts_updated", {"accounts": load_saved_accounts()})
    for log in state["logs"][-50:]:
        emit("log", log)


# ============================
# MAIN
# ============================
if __name__ == "__main__":
    load_panels()
    if not os.path.exists(SAVED_ACCOUNTS_JSON): save_saved_accounts([])
    if not os.path.exists(ACCOUNTS_LOG_TXT): open(ACCOUNTS_LOG_TXT, "a").close()

    if SOLVERCF_KEY:
        print(f"[solver] NextCaptcha configured ✅")
        print(f"[solver] type = RecaptchaV2TaskProxyless sitekey={VOYZ_RECAPTCHA_SITEKEY}")
    else:
        print("[solver] ⚠️ NEXTCAPTCHA_KEY not set")

    port = 5000
    host = os.environ.get("HOST", "0.0.0.0")
    if os.environ.get("PORT"):
        try: port = int(os.environ["PORT"])
        except ValueError: pass
        
    print(f"Voyz Panel → http://{host}:{port}")
    socketio.run(app, host=host, port=port, debug=False, allow_unsafe_werkzeug=True)