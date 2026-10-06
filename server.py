#!/usr/bin/env python3
"""
Call Center Scheduling Server
Connects to Builder Prime CRM + Google Maps Distance Matrix API
to generate ranked appointment scheduling options.

Usage:
  python3 server.py

Environment variables (set in .env or export before running):
  BUILDER_PRIME_API_KEY   - Your Builder Prime API key
  BUILDER_PRIME_BASE_URL  - Builder Prime base URL (default: https://app.builderprime.com/api/v1)
  GOOGLE_MAPS_API_KEY     - Google Maps API key (for drive time calculations)
  PORT                    - Server port (default: 8080)
  DEMO_MODE               - Set to "true" to use mock data without real API keys
"""

import json
import os
import math
import time
import threading
import urllib.request
import urllib.parse
import urllib.error
import secrets
import hashlib
from http.server import HTTPServer, BaseHTTPRequestHandler
from socketserver import ThreadingMixIn

class ThreadedHTTPServer(ThreadingMixIn, HTTPServer):
    daemon_threads = True
from datetime import datetime, timedelta, date
import random

# â"€â"€ Config â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€

# Load .env if present
def load_env():
    env_path = os.path.join(os.path.dirname(__file__), ".env")
    if os.path.exists(env_path):
        with open(env_path) as f:
            for line in f:
                line = line.strip()
                if line and not line.startswith("#") and "=" in line:
                    k, v = line.split("=", 1)
                    os.environ.setdefault(k.strip(), v.strip())

load_env()

BP_API_KEY   = os.environ.get("BUILDER_PRIME_API_KEY", "")
BP_BASE_URL  = os.environ.get("BUILDER_PRIME_BASE_URL", "https://app.builderprime.com/api/v1")
GMAPS_KEY    = os.environ.get("GOOGLE_MAPS_API_KEY", "")
PORT         = int(os.environ.get("PORT", 8080))
DEMO_MODE    = os.environ.get("DEMO_MODE", "true").lower() == "true"

# DATA_DIR: writable directory for config files that must survive deploys.
# On Render, set DATA_DIR=/data and attach a persistent disk at /data.
# Locally, defaults to the script's own directory (original behaviour).
_APP_DIR  = os.path.dirname(os.path.abspath(__file__))
_DATA_DIR = os.environ.get("DATA_DIR", _APP_DIR)

def _data(filename):
    """Return path inside DATA_DIR; copy default from app dir if not yet present."""
    dest = os.path.join(_DATA_DIR, filename)
    if not os.path.exists(dest):
        src = os.path.join(_APP_DIR, filename)
        if os.path.exists(src):
            import shutil
            os.makedirs(_DATA_DIR, exist_ok=True)
            shutil.copy2(src, dest)
    return dest

REP_CONFIG_FILE = _data("rep_config.json")

def load_rep_config():
    """Returns dict: {rep_id: {"enabled": bool, "priority": int 0-100}}"""
    if os.path.exists(REP_CONFIG_FILE):
        try:
            with open(REP_CONFIG_FILE) as f:
                return json.load(f).get("reps", {})
        except Exception:
            pass
    return {}

def save_rep_config(reps_dict):
    with open(REP_CONFIG_FILE, "w") as f:
        json.dump({"reps": reps_dict}, f)

# â"€â"€ Scheduling / class config â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€

SCHED_CONFIG_FILE = _data("scheduling_config.json")

_DEFAULT_CLASS_CFG = {"maxDaysOut": 7, "sameDayBufferMins": 30, "sameDayGapMins": 120, "maxDriveMins": 90, "shopAddresses": [], "maxShopDriveMins": 0}

_BUILTIN_CLASSES = {
    "Iowa":      {"maxDaysOut": 7, "sameDayBufferMins": 30, "sameDayGapMins": 120, "maxDriveMins": 90, "shopAddresses": [], "maxShopDriveMins": 0},
    "Ft Worth":  {"maxDaysOut": 7, "sameDayBufferMins": 30, "sameDayGapMins": 120, "maxDriveMins": 90, "shopAddresses": [], "maxShopDriveMins": 0},
    "Green Bay": {"maxDaysOut": 5, "sameDayBufferMins": 30, "sameDayGapMins": 120, "maxDriveMins": 90, "shopAddresses": [], "maxShopDriveMins": 0},
    "Milwaukee": {"maxDaysOut": 5, "sameDayBufferMins": 30, "sameDayGapMins": 120, "maxDriveMins": 90, "shopAddresses": [], "maxShopDriveMins": 0},
}

def load_sched_config():
    """Returns dict: { className: { maxDaysOut, sameDayBufferMins, sameDayGapMins, maxDriveMins } }"""
    if os.path.exists(SCHED_CONFIG_FILE):
        try:
            with open(SCHED_CONFIG_FILE) as f:
                return json.load(f).get("classes", dict(_BUILTIN_CLASSES))
        except Exception:
            pass
    return dict(_BUILTIN_CLASSES)

def save_sched_config(classes_dict):
    with open(SCHED_CONFIG_FILE, "w") as f:
        json.dump({"classes": classes_dict}, f)
    print(f"[Admin] Saved scheduling config: {list(classes_dict.keys())}", flush=True)

# â"€â"€ Auth â€" users & sessions â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€

USERS_FILE = _data("users.json")

def _hash_password(password, salt=None):
    if salt is None:
        salt = secrets.token_hex(16)
    dk = hashlib.pbkdf2_hmac("sha256", password.encode("utf-8"), salt.encode("utf-8"), 100_000)
    return f"{salt}:{dk.hex()}"

def _verify_password(password, stored):
    try:
        salt, _ = stored.split(":", 1)
        return secrets.compare_digest(_hash_password(password, salt), stored)
    except Exception:
        return False

def load_users():
    if os.path.exists(USERS_FILE):
        try:
            with open(USERS_FILE, encoding="utf-8-sig") as f:
                return json.load(f).get("users", {})
        except Exception:
            pass
    return {}

def save_users(users_dict):
    with open(USERS_FILE, "w") as f:
        json.dump({"users": users_dict}, f)

def _init_users():
    if not os.path.exists(USERS_FILE):
        default_admin_pw = "admin"
        default_user_pw  = "user"
        save_users({
            "admin": {"passwordHash": _hash_password(default_admin_pw), "role": "admin"},
            "user":  {"passwordHash": _hash_password(default_user_pw),  "role": "user"},
        })
        print("[Auth] Created default credentials:", flush=True)
        print(f"[Auth]   admin / {default_admin_pw}  (change via Settings â†' Users)", flush=True)
        print(f"[Auth]   user  / {default_user_pw}   (change via Settings â†' Users)", flush=True)

_sessions      = {}
_sessions_lock = threading.Lock()
SESSION_TTL    = 10 * 3600  # 10 hours

def _create_session(username, role):
    token = secrets.token_urlsafe(32)
    with _sessions_lock:
        _sessions[token] = {"username": username, "role": role, "expires": time.time() + SESSION_TTL}
    return token

def _get_session(token):
    if not token:
        return None
    with _sessions_lock:
        s = _sessions.get(token)
        if s and s["expires"] > time.time():
            return s
        if s:
            del _sessions[token]
    return None

def _invalidate_session(token):
    with _sessions_lock:
        _sessions.pop(token, None)

def _cleanup_sessions():
    """Periodically remove expired session entries from memory."""
    while True:
        time.sleep(3600)  # run every hour
        now = time.time()
        with _sessions_lock:
            expired = [t for t, s in _sessions.items() if s["expires"] <= now]
            for t in expired:
                del _sessions[t]
        if expired:
            print(f"[Auth] Cleaned up {len(expired)} expired sessions", flush=True)

# -- Brute-force login protection --
_login_attempts      = {}   # key -> {"count": N, "first": ts, "locked_until": ts}
_login_attempts_lock = threading.Lock()
_MAX_LOGIN_FAILS     = 5
_LOCKOUT_SECS        = 15 * 60   # 15 minutes
_ATTEMPT_WINDOW_SECS = 10 * 60   # rolling 10-minute window

def _is_login_locked(key):
    """Returns (locked, seconds_remaining)."""
    now = time.time()
    with _login_attempts_lock:
        e = _login_attempts.get(key)
        if not e:
            return False, 0
        if e.get("locked_until", 0) > now:
            return True, int(e["locked_until"] - now)
        if now - e.get("first", 0) > _ATTEMPT_WINDOW_SECS:
            del _login_attempts[key]
        return False, 0

def _record_login_fail(key):
    """Record a failed attempt; returns True if account is now locked."""
    now = time.time()
    with _login_attempts_lock:
        e = _login_attempts.get(key, {"count": 0, "first": now})
        if now - e.get("first", now) > _ATTEMPT_WINDOW_SECS:
            e = {"count": 0, "first": now}
        e["count"] = e.get("count", 0) + 1
        if e["count"] >= _MAX_LOGIN_FAILS:
            e["locked_until"] = now + _LOCKOUT_SECS
        _login_attempts[key] = e
        return e.get("locked_until", 0) > now

def _clear_login_attempts(key):
    with _login_attempts_lock:
        _login_attempts.pop(key, None)

# -- Endpoint rate limiting (per session token) --
_rate_limits      = {}   # (token, endpoint) -> [timestamps]
_rate_limits_lock = threading.Lock()

def _is_rate_limited(token, endpoint, max_calls, window_secs):
    """Return True if this token has exceeded max_calls to endpoint within window_secs."""
    now = time.time()
    key = (token, endpoint)
    with _rate_limits_lock:
        calls = _rate_limits.get(key, [])
        calls = [t for t in calls if now - t < window_secs]
        if len(calls) >= max_calls:
            _rate_limits[key] = calls
            return True
        calls.append(now)
        _rate_limits[key] = calls
        return False

def _cleanup_rate_limits():
    """Periodically prune stale rate limit entries."""
    while True:
        time.sleep(300)
        now = time.time()
        with _rate_limits_lock:
            stale = [k for k, v in _rate_limits.items() if not v or now - max(v) > 600]
            for k in stale:
                del _rate_limits[k]

# -- Allowed CORS origins --
_ALLOWED_ORIGINS = {
    "https://bam-scheduler.com",
    "http://localhost:8080",
    "http://127.0.0.1:8080",
}

# -- Client / appointment cache â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€

_client_cache  = []
_cache_ready   = False
_cache_lock    = threading.Lock()

_appt_cache      = {}   # grouped by repId
_appt_cache_ts   = 0    # epoch seconds when last fetched
_appt_cache_lock = threading.Lock()
APPT_CACHE_TTL   = 10 * 60  # 10 minutes

_rep_cache      = []
_rep_cache_ts   = 0
_rep_cache_lock = threading.Lock()
REP_CACHE_TTL   = 15 * 60  # 15 minutes

def get_cached_reps():
    """Return reps from cache if fresh, otherwise fetch and cache."""
    global _rep_cache, _rep_cache_ts
    with _rep_cache_lock:
        age = time.time() - _rep_cache_ts
        if _rep_cache and age < REP_CACHE_TTL:
            return list(_rep_cache)
    fresh = get_reps_bp()
    if fresh:
        with _rep_cache_lock:
            _rep_cache    = fresh
            _rep_cache_ts = time.time()
        return fresh
    with _rep_cache_lock:
        return list(_rep_cache)

def get_cached_appointments(start_str, end_str):
    """Return appointments from cache if fresh, otherwise fetch and cache.
    Pre-geocodes all appointment addresses so scheduling never blocks on Maps calls."""
    global _appt_cache, _appt_cache_ts
    with _appt_cache_lock:
        age = time.time() - _appt_cache_ts
        if _appt_cache and age < APPT_CACHE_TTL:
            return _appt_cache
    fresh = get_all_appointments_bp(start_str, end_str)
    if fresh:
        _pregeocode_appointments(fresh)
        with _appt_cache_lock:
            _appt_cache    = fresh
            _appt_cache_ts = time.time()
        return fresh
    with _appt_cache_lock:
        return _appt_cache  # return stale rather than empty

def _pregeocode_appointments(grouped):
    """Geocode all appointment addresses in the background so scheduling is fast."""
    count = 0
    for appts in grouped.values():
        for a in appts:
            if not a.get("lat") and a.get("address"):
                lat, lng = geocode_address(a["address"])
                a["lat"], a["lng"] = lat, lng
                if lat:
                    count += 1
    if count:
        print(f"[Cache] Pre-geocoded {count} appointment addresses", flush=True)

CACHE_FILE    = os.path.join(_DATA_DIR, "client_cache.json")
CACHE_MAX_AGE = 6 * 3600  # seconds before disk cache is considered stale

def _save_cache_to_disk(clients):
    try:
        tmp = CACHE_FILE + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump({"saved_at": time.time(), "clients": clients}, f)
        os.replace(tmp, CACHE_FILE)
        print(f"[Cache] Saved {len(clients)} clients to disk", flush=True)
    except Exception as exc:
        print(f"[Cache] Disk save failed: {exc}", flush=True)

def _load_cache_from_disk():
    """Return cached clients if disk file is fresh, else None."""
    try:
        if not os.path.exists(CACHE_FILE):
            return None
        with open(CACHE_FILE, encoding="utf-8") as f:
            data = json.load(f)
        age = time.time() - data.get("saved_at", 0)
        if age > CACHE_MAX_AGE:
            print(f"[Cache] Disk cache is {int(age/3600)}h old, refreshing from BP", flush=True)
            return None
        clients = data.get("clients", [])
        print(f"[Cache] Loaded {len(clients)} clients from disk ({int(age/60)}m old)", flush=True)
        return clients
    except Exception as exc:
        print(f"[Cache] Disk read failed: {exc}", flush=True)
        return None

def _fetch_clients_from_bp():
    """Download all clients from BP. Returns list; updates in-memory cache incrementally."""
    global _client_cache, _cache_ready
    print("[Cache] Downloading clients from BP...", flush=True)
    all_clients = []
    for page in range(300):
        batch = None
        for attempt in range(3):
            try:
                raw   = bp_request("/api/clients", {"limit": 100, "page": page})
                batch = raw.get("data", raw) if isinstance(raw, dict) else raw
                if not isinstance(batch, list):
                    batch = []
                break
            except urllib.error.HTTPError as e:
                if e.code == 429 and attempt < 2:
                    wait = 60 * (attempt + 1)
                    print(f"[Cache] 429 on page {page}, waiting {wait}s...", flush=True)
                    time.sleep(wait)
                else:
                    print(f"[Cache] page {page} HTTP {e.code}, stopping", flush=True)
                    batch = None
                    break
            except Exception as e:
                print(f"[Cache] page {page} error: {e}", flush=True)
                batch = None
                break
        if batch is None:
            break
        if not batch:
            break
        all_clients.extend([normalize_contact(c) for c in batch])
        if page % 10 == 0 or not _cache_ready:
            with _cache_lock:
                _client_cache = list(all_clients)
                _cache_ready  = True
        if len(batch) < 100:
            break
        time.sleep(0.15)
    return all_clients

def _load_client_cache():
    global _client_cache, _cache_ready
    if DEMO_MODE or not BP_API_KEY:
        with _cache_lock:
            _client_cache = MOCK_CONTACTS
            _cache_ready  = True
        return

    # Fast path: serve from disk if cache is fresh
    disk_clients = _load_cache_from_disk()
    if disk_clients:
        with _cache_lock:
            _client_cache = disk_clients
            _cache_ready  = True
        print(f"[Cache] Ready -- {len(disk_clients)} clients (from disk)", flush=True)
        return

    # Slow path: download from BP, then save to disk
    all_clients = _fetch_clients_from_bp()
    if all_clients:
        _save_cache_to_disk(all_clients)
    with _cache_lock:
        _client_cache = all_clients
        _cache_ready  = True
    print(f"[Cache] Ready -- {len(all_clients)} clients loaded", flush=True)

def _cache_refresh_loop():
    """Background thread: load on startup, then refresh from BP every 6 hours."""
    _load_client_cache()  # initial load (disk or BP)
    while True:
        time.sleep(6 * 3600)
        print("[Cache] Starting scheduled 6h refresh from BP...", flush=True)
        all_clients = _fetch_clients_from_bp()
        if all_clients:
            _save_cache_to_disk(all_clients)
            with _cache_lock:
                global _client_cache
                _client_cache = all_clients
            print(f"[Cache] Refresh complete -- {len(all_clients)} clients", flush=True)

def _warmup_caches():
    """On startup: pre-load reps and geocode all appointment addresses so the
    first real request is fast instead of hitting Google Maps 100+ times live."""
    if DEMO_MODE or not BP_API_KEY:
        return
    # Warm rep cache
    get_cached_reps()
    print("[Cache] Reps warmed.", flush=True)
    # Warm appointment cache + geocode all addresses
    sched_cfg  = load_sched_config()
    max_window = max((v.get("maxDaysOut", 7) for v in sched_cfg.values()), default=7)
    end_str    = (date.today() + timedelta(days=max(14, max_window + 1))).isoformat()
    get_cached_appointments(date.today().isoformat(), end_str)
    print("[Cache] Appointments warmed and geocoded.", flush=True)

# â"€â"€ Builder Prime API helpers â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€

def bp_request(endpoint, params=None):
    url = BP_BASE_URL.rstrip("/") + endpoint
    if params:
        url += "?" + urllib.parse.urlencode(params)
    req = urllib.request.Request(url, headers={"x-api-key": BP_API_KEY})
    with urllib.request.urlopen(req, timeout=15) as resp:
        return json.loads(resp.read().decode())

def search_clients_bp(query):
    try:
        with _cache_lock:
            clients = list(_client_cache)
        if not clients:
            return []
        ql = query.lower()
        results = [c for c in clients if
                   ql in (c.get("phone") or "").replace("-","").replace(" ","") or
                   ql in (c.get("address") or "").lower() or
                   ql in (c.get("firstName") or "").lower() or
                   ql in (c.get("lastName")  or "").lower() or
                   ql in (c.get("fullName")  or "").lower()]
        return results[:20]
    except Exception as e:
        print(f"[BP] contact search failed: {e}")
        return None

def get_client_bp(client_id):
    """Fetch a single client by ID."""
    try:
        raw = bp_request(f"/api/clients/{client_id}")
        c = raw if isinstance(raw, dict) and "firstName" in raw else raw.get("data", raw)
        return normalize_contact(c)
    except Exception as e:
        print(f"[BP] client fetch failed: {e}")
        return None

def get_reps_bp():
    """
    Fetch active sales reps from Builder Prime.
    Paginates all employee pages, filters to active salespeople, deduplicates by name.
    """
    try:
        all_employees = []
        for page in range(10):   # up to 1000 employees
            raw   = bp_request("/api/employees/v1", {"limit": 100, "page": page})
            batch = raw.get("data", raw) if isinstance(raw, dict) else raw
            if not batch:
                break
            all_employees.extend(batch)
            if len(batch) < 100:
                break

        # Active + current + flagged as salesperson in BP
        eligible = [e for e in all_employees if
                    e.get("isCurrentEmployee") and
                    e.get("isActiveUser") and
                    e.get("isSalesPerson")]

        # If nobody is flagged isSalesPerson, fall back to sales-calendar employees
        if not eligible:
            eligible = [e for e in all_employees if
                        e.get("isCurrentEmployee") and
                        e.get("isActiveUser") and
                        e.get("showInSalesCalendarByDefault")]

        # Deduplicate by full name â€" keep isSalesPerson=true record when both exist
        name_map = {}
        for e in eligible:
            name = f"{e.get('firstName','')} {e.get('lastName','')}".strip().lower()
            existing = name_map.get(name)
            if not existing or (e.get("isSalesPerson") and not existing.get("isSalesPerson")):
                name_map[name] = e

        return [normalize_rep(r) for r in name_map.values()]
    except Exception as e:
        print(f"[BP] reps fetch failed: {e}")
        return None

def get_all_appointments_bp(start_date_str, end_date_str):
    """
    Fetch ALL meetings paginated and return them grouped by employeeId.
    """
    try:
        from_ms = int(datetime.fromisoformat(start_date_str).timestamp() * 1000)
        to_ms   = int(datetime.fromisoformat(end_date_str).timestamp() * 1000) + 86_400_000
        all_appts = []
        for page in range(20):  # up to 2000 appointments
            raw = bp_request("/api/meetings/v1", {
                "start-date-from": from_ms,
                "start-date-to":   to_ms,
                "limit": 100,
                "page":  page,
            })
            batch = raw.get("data", []) if isinstance(raw, dict) else raw
            if not batch:
                break
            all_appts.extend(batch)
            if len(batch) < 100:
                break
        grouped = {}
        for a in all_appts:
            if a.get("isMeetingCancelled"):
                continue
            na = normalize_appointment(a)
            grouped.setdefault(na["repId"], []).append(na)
        print(f"[BP] Fetched {len(all_appts)} appointments, {len(grouped)} reps with bookings", flush=True)
        return grouped
    except Exception as e:
        print(f"[BP] appointments fetch failed: {e}")
        return None

def normalize_contact(c):
    city  = c.get("city", "")
    state = c.get("state", "")
    parts = [c.get("addressLine1", ""), city, state, c.get("zip", "")]
    address = ", ".join(p for p in parts if p)
    first = c.get("firstName", "")
    last  = c.get("lastName", "")
    return {
        "id":        str(c.get("id", c.get("clientId", ""))),
        "firstName": first,
        "lastName":  last,
        "fullName":  f"{first} {last}".strip(),
        "phone":     c.get("phoneNumber", c.get("homePhoneNumber", "")),
        "address":   address,
        "city":      city,
        "state":     state,
        "lat":       c.get("lat"),
        "lng":       c.get("lng"),
        "leadStatusName":         c.get("leadStatusName", ""),
        "leadStatusCategoryName": c.get("leadStatusCategoryName", ""),
        "createdDate":            c.get("createdDate"),
        "lastModifiedDate":       c.get("lastModifiedDate"),
    }

# Clients with createdDate at or before this timestamp used the June 2024 migration date
# (unreliable for filtering). Value = Dec 30, 2025 00:00:00 UTC.
MIGRATION_CUTOFF_TS = 1767139200000

_MILWAUKEE_WI_CITIES = frozenset([
    "milwaukee", "brookfield", "oak creek", "kenosha", "racine",
    "waukesha", "west allis", "wauwatosa", "menomonee falls",
    "new berlin", "pewaukee", "hartland", "oconomowoc", "muskego",
    "franklin", "south milwaukee", "cudahy", "greenfield", "greendale",
    "hales corners", "st. francis", "germantown", "mequon", "richfield",
    "sussex", "mukwonago", "waterford", "elkhorn", "lake geneva",
    "delavan", "delafield", "wales", "burlington", "union grove",
    "watertown", "beaver dam", "janesville", "beloit",
])

def client_area(c):
    state = (c.get("state") or "").upper().strip()
    city  = (c.get("city") or "").lower().strip()
    if state == "IA": return "Iowa"
    if state == "TX": return "Ft Worth"
    if state == "WI":
        return "Milwaukee" if city in _MILWAUKEE_WI_CITIES else "Green Bay"
    return None

_SOLD_EXACT = frozenset([
    "job sold", "job in progress", "customer", "customer signed",
    "sold", "scheduled", "in progress", "complete",
])
_SOLD_CATEGORIES = frozenset(["customers", "production"])

_SKIP_STATUSES = frozenset([
    # Appointment not yet run or never set
    "appointment set", "appointment confirmed",
    "appointment not set 2-7", "appointment not set 7-30",
    "appointment not set 30-60", "appointment not set 60+",
    # Cancelled / reset (no demo ran)
    "appt cxl (reset)", "appt cxl (reset) 30", "appt cxl (reset) 60+",
    # Other non-demo statuses
    "bad data", "out of area", "no demo", "call backs", "new leads",
])

def is_sold_client(c):
    status   = (c.get("leadStatusName") or "").lower().strip()
    category = (c.get("leadStatusCategoryName") or "").lower().strip()
    if category in _SOLD_CATEGORIES:
        return True
    if status in _SOLD_EXACT:
        return True
    for kw in ("job sold", "customer signed", "job in progress"):
        if kw in status:
            return True
    return False

def is_demo_lead(c):
    """True if this client had an actual demo/sales interaction (appointment ran)."""
    status   = (c.get("leadStatusName") or "").lower().strip()
    category = (c.get("leadStatusCategoryName") or "").lower().strip()
    if "historic" in status or "historic" in category:
        return False
    if status in _SKIP_STATUSES:
        return False
    if category in ("customers", "production", "sales", "leads", "prospects"):
        return True
    return False

def normalize_rep(r):
    colors = ["#6366f1","#10b981","#f59e0b","#ec4899","#3b82f6","#8b5cf6"]
    rep_id = str(r.get("id", ""))
    color  = colors[hash(rep_id) % len(colors)]
    return {
        "id":       rep_id,
        "name":     f"{r.get('firstName','')} {r.get('lastName','')}".strip(),
        "phone":    r.get("phone", ""),
        "priority": r.get("priority", 99),
        "color":    color,
    }

def normalize_appointment(a):
    start_ms = a.get("startDateTime", 0)
    end_ms   = a.get("endDateTime", start_ms + 5_400_000)
    start_dt = datetime.fromtimestamp(start_ms / 1000)
    dur_hrs  = (end_ms - start_ms) / 3_600_000
    return {
        "id":           str(a.get("id", "")),
        "repId":        str(a.get("employeeId", "")),
        "date":         start_dt.date().isoformat(),
        "startHour":    start_dt.hour + start_dt.minute / 60,
        "durationHours": round(dur_hrs, 2),
        "lat":          None,   # BP meetings have address string, not coords
        "lng":          None,
        "address":      a.get("location", ""),
        "customerName": f"{a.get('clientFirstName','')} {a.get('clientLastName','')}".strip(),
    }

# â"€â"€ Google Maps helpers â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€

_drive_cache = {}

def get_drive_time_minutes(origin_lat, origin_lng, dest_lat, dest_lng, departure_dt=None):
    """
    Returns drive time in minutes using Google Maps Distance Matrix API.
    Pass departure_dt (datetime) to get traffic-aware travel time.
    Cache key includes weekday + 30-min time bucket so Mon 8am and Fri 5pm cache separately.
    Falls back to Haversine estimate on failure.
    """
    # Round coords to ~100m precision to maximise cache hits
    coord_key = (round(origin_lat, 3), round(origin_lng, 3),
                 round(dest_lat,   3), round(dest_lng,   3))
    # Time bucket: (weekday 0-6, 30-min slot 0-47) — repeats weekly so cache stays useful
    if departure_dt is not None:
        time_bucket = (departure_dt.weekday(), departure_dt.hour * 2 + departure_dt.minute // 30)
    else:
        time_bucket = None
    key         = (coord_key, time_bucket)
    fallback_key = (coord_key, None)  # traffic-free cached result

    if key in _drive_cache:
        return _drive_cache[key]

    # If a traffic-free result is already cached, use it rather than making a new Maps call.
    # The traffic-aware result will be stored the first time this (route, time) is actually computed.
    if time_bucket is not None and fallback_key in _drive_cache:
        return _drive_cache[fallback_key]

    if not GMAPS_KEY:
        result = haversine_drive_estimate(origin_lat, origin_lng, dest_lat, dest_lng)
        _drive_cache[key] = result
        return result
    try:
        api_params = {
            "origins":      f"{origin_lat},{origin_lng}",
            "destinations": f"{dest_lat},{dest_lng}",
            "mode": "driving",
            "key": GMAPS_KEY,
        }
        if departure_dt is not None:
            api_params["departure_time"] = int(departure_dt.timestamp())
        params = urllib.parse.urlencode(api_params)
        url = f"https://maps.googleapis.com/maps/api/distancematrix/json?{params}"
        with urllib.request.urlopen(url, timeout=8) as resp:
            data = json.loads(resp.read().decode())
        element = data["rows"][0]["elements"][0]
        if element["status"] == "OK":
            # Prefer traffic-aware duration when available
            if "duration_in_traffic" in element:
                result = element["duration_in_traffic"]["value"] // 60
            else:
                result = element["duration"]["value"] // 60
            _drive_cache[key] = result
            # Also populate the fallback key so other time-buckets for this route
            # skip the API entirely and use this result (avoids per-slot API storms).
            if fallback_key not in _drive_cache:
                _drive_cache[fallback_key] = result
            return result
    except Exception as e:
        print(f"[Maps] drive time failed: {e}")
    result = haversine_drive_estimate(origin_lat, origin_lng, dest_lat, dest_lng)
    _drive_cache[key] = result
    if fallback_key not in _drive_cache:
        _drive_cache[fallback_key] = result
    return result

def haversine_drive_estimate(lat1, lng1, lat2, lng2):
    """Rough drive time estimate: straight-line km x 1.4 road factor / 50 km/h."""
    R = 6371
    dlat = math.radians(lat2 - lat1)
    dlng = math.radians(lng2 - lng1)
    a = math.sin(dlat/2)**2 + math.cos(math.radians(lat1)) * math.cos(math.radians(lat2)) * math.sin(dlng/2)**2
    km = R * 2 * math.asin(math.sqrt(a))
    drive_km = km * 1.4
    minutes = (drive_km / 50) * 60
    return round(minutes)

_geocode_cache = {}

def geocode_address(address):
    """Geocode an address string to (lat, lng). Results cached in memory."""
    if not address:
        return None, None
    if address in _geocode_cache:
        return _geocode_cache[address]
    if not GMAPS_KEY:
        _geocode_cache[address] = (None, None)
        return None, None
    try:
        params = urllib.parse.urlencode({"address": address, "key": GMAPS_KEY})
        url = f"https://maps.googleapis.com/maps/api/geocode/json?{params}"
        with urllib.request.urlopen(url, timeout=8) as resp:
            data = json.loads(resp.read().decode())
        status = data.get("status", "UNKNOWN")
        if status == "OK" and data.get("results"):
            loc = data["results"][0]["geometry"]["location"]
            result = loc["lat"], loc["lng"]
            _geocode_cache[address] = result
            return result
        else:
            print(f"[Maps] geocode status={status!r} for {address!r} (error_message={data.get('error_message','')})")
    except Exception as e:
        print(f"[Maps] geocode failed: {e}")
    _geocode_cache[address] = (None, None)
    return None, None

# â"€â"€ Mock data (used when DEMO_MODE=true or no API key) â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€

MOCK_CONTACTS = [
    {"id":"1","firstName":"Alice","lastName":"Johnson","phone":"555-0101","address":"123 Oak St, Des Moines, IA 50309","lat":41.5868,"lng":-93.6250},
    {"id":"2","firstName":"Bob","lastName":"Smith","phone":"555-0102","address":"456 Maple Ave, Cedar Rapids, IA 52401","lat":41.9779,"lng":-91.6656},
    {"id":"3","firstName":"Carol","lastName":"Davis","phone":"555-0103","address":"789 Pine Rd, Ames, IA 50010","lat":42.0308,"lng":-93.6319},
    {"id":"4","firstName":"David","lastName":"Wilson","phone":"555-0104","address":"321 Elm St, Iowa City, IA 52240","lat":41.6611,"lng":-91.5302},
]

MOCK_REPS = [
    {"id":"rep1","name":"Tyler Cleven","phone":"","priority":1,"color":"#6366f1"},
    {"id":"rep2","name":"Chris Wesolowski","phone":"","priority":2,"color":"#10b981"},
    {"id":"rep3","name":"Matt Stenberg","phone":"","priority":3,"color":"#f59e0b"},
]

MOCK_APPOINTMENTS = {
    "rep1": [{"id":"a1","repId":"rep1","date": date.today().isoformat(),"startHour":10,"durationHours":1,"address":"100 Main St, Des Moines, IA","lat":41.59,"lng":-93.62,"customerName":"Demo Customer"}],
    "rep2": [],
    "rep3": [],
}

# â"€â"€ Scheduling helpers â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€

WORK_START = 9   # 9 AM
WORK_END   = 18  # 6 PM last slot
APPT_DUR   = 0.75 # assumed appointment duration in hours (45 min) â€" overridden per rep
# Drive time above this threshold triggers a "clean day" suggestion
CLEAN_DAY_DRIVE_THRESHOLD = int(os.environ.get("CLEAN_DAY_DRIVE_THRESHOLD", 60))

REP_CLASS_CITIES = {
    "iowa":      "Des Moines, IA",
    "ft worth":  "Fort Worth, TX",
    "green bay": "Green Bay, WI",
    "milwaukee": "Milwaukee, WI",
}

def rep_home_drive_to(rep, dest_lat, dest_lng, departure_dt=None):
    """Drive time from rep's home address (or class city fallback) to destination. Returns (mins, origin_label)."""
    home = rep.get("homeAddress", "").strip()
    cls  = rep.get("repClass", "").strip().lower()
    # Try home address first
    if home:
        hlat, hlng = geocode_address(home)
        if hlat and hlng:
            return get_drive_time_minutes(hlat, hlng, dest_lat, dest_lng, departure_dt), home
        print(f"[Maps] rep {rep.get('id')} homeAddress geocode failed for {home!r}, trying class city fallback")
    # Fall back to class city
    city = REP_CLASS_CITIES.get(cls, "")
    if city:
        hlat, hlng = geocode_address(city)
        if hlat and hlng:
            return get_drive_time_minutes(hlat, hlng, dest_lat, dest_lng, departure_dt), city
        print(f"[Maps] rep {rep.get('id')} class city geocode also failed for {city!r}")
    return 9999, ""  # unknown origin — exclude from scheduling (no homeAddress or repClass configured)

def find_schedule_options(customer_lat, customer_lng, reps, all_appointments,
                           class_configs=None, days_to_look=7):
    """
    Core scheduling algorithm with per-class scheduling intelligence rules.

    Per-class rules (from class_configs):
      maxDaysOut        - how many days ahead to look for this class
      maxDriveMins      - on busy days, customer must be within this drive time of at
                          least one adjacent appointment (empty days exempt)
      sameDayBufferMins - drive-time threshold from adjacent appointment (applied only
                          when the schedule gap around the slot is < sameDayGapMins)
      sameDayGapMins    - if the open window around a slot is >= this many minutes,
                          bypass the sameDayBufferMins check entirely (rep has time
                          to travel); empty days always bypass since gap = full day
    """
    if class_configs is None:
        class_configs = {}

    candidates = []

    sorted_reps = sorted(reps, key=lambda r: -r.get("priority_pct", 50))

    # Pre-compute out-of-area status per class (customer distance vs nearest shop address).
    # This runs once per class, not once per slot, to avoid redundant Maps calls.
    class_ota = {}
    for _rep in sorted_reps:
        _rc = _rep.get("repClass", "")
        if _rc in class_ota:
            continue
        _ccfg      = class_configs.get(_rc, _DEFAULT_CLASS_CFG)
        _shops     = _ccfg.get("shopAddresses", [])
        _max_shop  = _ccfg.get("maxShopDriveMins", 0)
        if not _shops or not _max_shop:
            class_ota[_rc] = None
            continue
        _min_drive = None
        for _addr in _shops:
            _addr = _addr.strip()
            if not _addr:
                continue
            _slat, _slng = geocode_address(_addr)
            if _slat and _slng:
                _d = get_drive_time_minutes(_slat, _slng, customer_lat, customer_lng)
                if _min_drive is None or _d < _min_drive:
                    _min_drive = _d
        if _min_drive is not None:
            _ota_flag = _min_drive > _max_shop
            print(f"[OOA] class={_rc!r} shopDrive={_min_drive}min threshold={_max_shop}min outOfArea={_ota_flag}", flush=True)
            class_ota[_rc] = {
                "shopDriveMins":    _min_drive,
                "outOfArea":        _ota_flag,
                "maxShopDriveMins": _max_shop,
            }
        else:
            print(f"[OOA] class={_rc!r} -- shop geocode/drive failed, skipping OOA check", flush=True)
            class_ota[_rc] = None

    # Global ceiling = max maxDaysOut across all active rep classes
    global_max_days = max(
        (class_configs.get(r.get("repClass", ""), _DEFAULT_CLASS_CFG).get("maxDaysOut", days_to_look)
         for r in reps),
        default=days_to_look
    )

    now = datetime.now()
    today = date.today()
    current_time = now.hour + now.minute / 60

    # Two-pass loop: first pass applies all distance rules; if the address is out-of-area
    # for every rep and no candidates are found, the second relaxed pass skips drive-distance
    # filters AND extends the look-ahead to 14 days so the user always gets options.
    for relax_drive in [False, True]:
        if relax_drive and candidates:
            break  # normal pass succeeded â€" skip relaxed pass

        # In the relaxed pass extend the horizon so we find future open days even if
        # everyone is booked in their normal window.
        days_ceiling = max(global_max_days, 14) if relax_drive else global_max_days

        for day_offset in range(days_ceiling + 1):
            target_date = today + timedelta(days=day_offset)
            if target_date.weekday() == 6:  # skip Sunday only; Saturday is a workday
                continue

            for rep in sorted_reps:
                # Per-class scheduling rules
                rep_class      = rep.get("repClass", "")
                class_cfg      = class_configs.get(rep_class, _DEFAULT_CLASS_CFG)
                max_days       = class_cfg.get("maxDaysOut", days_to_look)
                same_day_buf   = class_cfg.get("sameDayBufferMins", 30)
                same_day_gap   = class_cfg.get("sameDayGapMins", 120)
                max_drive      = class_cfg.get("maxDriveMins", 90)

                # In the relaxed pass ignore each rep's normal maxDaysOut window so every
                # rep can surface options up to the extended 14-day horizon.
                if not relax_drive and day_offset > max_days:
                    continue  # beyond this class's look-ahead window

                rep_appts = [a for a in all_appointments.get(rep["id"], [])
                             if a["date"] == target_date.isoformat()]
                rep_appts.sort(key=lambda a: a["startHour"])
                has_appts = bool(rep_appts)

                appt_dur   = rep.get("apptDurationMins", 45) / 60.0
                open_slots = find_open_slots(rep_appts, appt_dur)

                for slot_hour in open_slots:
                    # Skip slots that have already started or passed today
                    if day_offset == 0 and slot_hour < current_time:
                        continue
                    # Find the appointment immediately before this slot (drive origin)
                    preceding = None
                    for appt in reversed(rep_appts):
                        if appt["startHour"] + appt["durationHours"] <= slot_hour:
                            preceding = appt
                            break

                    if preceding:
                        plat, plng = preceding.get("lat"), preceding.get("lng")
                        if not plat and preceding.get("address"):
                            plat, plng = geocode_address(preceding["address"])
                            preceding["lat"], preceding["lng"] = plat, plng  # cache
                        preceding_end = preceding["startHour"] + preceding["durationHours"]
                        # Departure = moment rep leaves prior appointment heading to customer
                        pre_depart_dt = datetime.combine(target_date, datetime.min.time()) + timedelta(hours=preceding_end)
                        if plat and plng:
                            drive_mins = get_drive_time_minutes(
                                plat, plng, customer_lat, customer_lng, pre_depart_dt
                            )
                            drive_from = preceding
                        else:
                            drive_mins, _ = rep_home_drive_to(rep, customer_lat, customer_lng, pre_depart_dt)
                            drive_from = None

                        # Skip slot if rep can't physically get there in time
                        available_mins = (slot_hour - preceding_end) * 60
                        if drive_mins > available_mins:
                            continue
                    else:
                        # No prior appointment — rep drives from home at slot start time
                        home_depart_dt = datetime.combine(target_date, datetime.min.time()) + timedelta(hours=slot_hour)
                        drive_mins, _ = rep_home_drive_to(rep, customer_lat, customer_lng, home_depart_dt)
                        drive_from = None

                        # For today's first slot: check rep can leave home/class and arrive in time
                        if day_offset == 0:
                            available_mins = (slot_hour - current_time) * 60
                            if drive_mins > available_mins:
                                continue

                    # Find the appointment immediately AFTER this slot
                    slot_end = slot_hour + appt_dur
                    following = None
                    for appt in rep_appts:
                        if appt["startHour"] >= slot_end:
                            following = appt
                            break

                    # Drive from customer to following appointment
                    post_drive_mins = None
                    post_drive_ok   = True
                    post_drive_addr = None
                    if following:
                        flat, flng = following.get("lat"), following.get("lng")
                        if not flat and following.get("address"):
                            flat, flng = geocode_address(following["address"])
                            following["lat"], following["lng"] = flat, flng  # cache
                        # Departure = when the new appointment ends, heading to next
                        post_depart_dt = datetime.combine(target_date, datetime.min.time()) + timedelta(hours=slot_end)
                        if flat and flng:
                            post_drive_mins = get_drive_time_minutes(
                                customer_lat, customer_lng, flat, flng, post_depart_dt
                            )
                            buffer_mins = (following["startHour"] - slot_end) * 60
                            post_drive_ok   = post_drive_mins <= buffer_mins
                            post_drive_addr = following["address"]

                    # Hard geographic cap: even in relaxed pass, exclude reps whose home/class
                    # city is more than 4x maxDriveMins from the customer (prevents Wisconsin
                    # reps from surfacing for Texas customers when Ft Worth reps are fully booked).
                    if relax_drive:
                        home_dist, _ = rep_home_drive_to(rep, customer_lat, customer_lng)
                        if home_dist > max_drive * 4:
                            continue

                    if not relax_drive:
                        # Clean-day maxDrive check: rep has no appointments today, so drive
                        # is from home. Apply the same distance cap.
                        if not has_appts and drive_mins > max_drive:
                            continue

                        # Overall max drive filter: on busy days, customer must be within
                        # maxDriveMins of at least one adjacent appointment (or home when
                        # no preceding appointment exists).
                        if has_appts:
                            pre_ok  = drive_mins <= max_drive  # drive_mins is from appt or home
                            post_ok = post_drive_mins is not None and post_drive_mins <= max_drive
                            if not pre_ok and not post_ok:
                                continue  # customer too far from rep's area on this day

                        # Same-day adjacency buffer: if the open window around this slot is
                        # smaller than sameDayGapMins, the rep doesn't have enough free time
                        # to travel far â€" customer must be within sameDayBufferMins of an
                        # adjacent appointment. If the gap is large enough (or the day is
                        # empty = infinite gap), the buffer is bypassed entirely.
                        if has_appts:
                            preceding_end    = (preceding["startHour"] + preceding["durationHours"]) if preceding else WORK_START
                            following_start  = following["startHour"] if following else WORK_END
                            gap_mins         = (following_start - preceding_end) * 60
                            if gap_mins < same_day_gap:
                                pre_close  = drive_mins <= same_day_buf
                                post_close = (post_drive_mins is not None and post_drive_mins <= same_day_buf)
                                if not pre_close and not post_close:
                                    continue  # tight schedule â€" customer too far from rep's area today

                    # Hard filter: if rep can't reach next appointment on time, skip.
                    # In the relaxed pass we keep showing the slot (flagged red) so the
                    # user has something to work with â€" they can pick a different time.
                    if not relax_drive and post_drive_mins is not None and not post_drive_ok:
                        continue

                    priority_pct = rep.get("priority_pct", 50)

                    candidates.append({
                        "rep": rep,
                        "date": target_date.isoformat(),
                        "dayLabel": format_day_label(target_date),
                        "hour": slot_hour,
                        "timeLabel": format_time(slot_hour),
                        "driveMinutes":     drive_mins,
                        "driveFromAddress": drive_from["address"] if drive_from else (rep.get("homeAddress") or "Start of day"),
                        "postDriveMinutes": post_drive_mins,
                        "postDriveAddress": post_drive_addr,
                        "postDriveOk":      post_drive_ok,
                        "areaProbability": estimate_area_probability(
                            customer_lat, customer_lng, target_date, all_appointments
                        ),
                        "daysOut": day_offset,
                        "shopDriveMins": (class_ota.get(rep_class) or {}).get("shopDriveMins"),
                        "outOfArea":     (class_ota.get(rep_class) or {}).get("outOfArea", False),
                        # Score: days out is primary, then pre+post drive time, then priority pct
                        "_score": day_offset * 10 + drive_mins / 5 + (100 - priority_pct) / 20,
                    })

        pass_label = "RELAXED" if relax_drive else "NORMAL"
        print(f"[Schedule] {pass_label} pass â†' {len(candidates)} candidates", flush=True)
        if candidates:
            break  # found results in this pass

    # Rank all candidates, take best 3
    candidates.sort(key=lambda o: o["_score"])
    top3 = candidates[:3]

    # Extra options: all remaining valid candidates beyond the top 3.
    extra_options = candidates[3:]

    # Clean-day suggestion: if the 3 best options all have long drives, surface a
    # slot 1-2 days out where the rep starts fresh geographically.
    all_long_drive = top3 and all(o["driveMinutes"] >= CLEAN_DAY_DRIVE_THRESHOLD for o in top3)
    if all_long_drive:
        clean = find_clean_day_option(customer_lat, customer_lng, sorted_reps, all_appointments, class_configs=class_configs)
        if clean:
            _ota_c = class_ota.get(clean["rep"].get("repClass", ""))
            clean["shopDriveMins"] = _ota_c["shopDriveMins"] if _ota_c else None
            clean["outOfArea"]     = _ota_c["outOfArea"]     if _ota_c else False
            top3.append(clean)

    return {"options": top3, "extraOptions": extra_options}

def find_open_slots(rep_appts, appt_dur=APPT_DUR):
    """Return list of start times (in 0.5-hour increments) that are open in the workday."""
    slots = []
    h = float(WORK_START)
    while h < WORK_END:
        slot_end = h + appt_dur
        conflict = any(
            a["startHour"] < slot_end and a["startHour"] + a["durationHours"] > h
            for a in rep_appts
        )
        if not conflict:
            slots.append(h)
        h += 0.5
    return slots

def find_clean_day_option(customer_lat, customer_lng, sorted_reps, all_appointments,
                          class_configs=None, days_ahead=1):
    """
    Return the earliest slot where the rep has ZERO existing appointments that day
    and the drive from home/class is within maxDriveMins.
    Shown as an additional suggestion when all top-3 options have long drives.
    """
    if class_configs is None:
        class_configs = {}
    today = date.today()
    for day_offset in range(days_ahead, days_ahead + 7):
        target_date = today + timedelta(days=day_offset)
        if target_date.weekday() == 6:  # skip Sunday only
            continue
        for rep in sorted_reps:
            rep_appts = [a for a in all_appointments.get(rep["id"], [])
                         if a["date"] == target_date.isoformat()]
            if rep_appts:
                continue  # not a clean day â€" rep already has bookings

            rep_class = rep.get("repClass", "")
            class_cfg = class_configs.get(rep_class, _DEFAULT_CLASS_CFG)
            max_drive = class_cfg.get("maxDriveMins", 90)

            # On a clean day the rep leaves home at the first available slot time
            appt_dur   = rep.get("apptDurationMins", 45) / 60.0
            open_slots = find_open_slots([], appt_dur)
            if not open_slots:
                continue
            h = open_slots[0]
            home_depart_dt = datetime.combine(target_date, datetime.min.time()) + timedelta(hours=h)
            drive_mins, origin = rep_home_drive_to(rep, customer_lat, customer_lng, home_depart_dt)
            if drive_mins > max_drive:
                continue  # rep's home is too far for a clean-day trip
            return {
                "rep": rep,
                "date": target_date.isoformat(),
                "dayLabel": format_day_label(target_date),
                "hour": h,
                "timeLabel": format_time(h),
                "driveMinutes":     int(drive_mins),
                "driveFromAddress": origin or rep.get("homeAddress") or "Home",
                "postDriveMinutes": None,
                "postDriveAddress": None,
                "postDriveOk":      True,
                "areaProbability": estimate_area_probability(
                    customer_lat, customer_lng, target_date, all_appointments
                ),
                "isCleanDay": True,
                "daysOut": day_offset,
                "_score": day_offset * 10 + drive_mins / 5,
            }
    return None

def estimate_area_probability(customer_lat, customer_lng, target_date, all_appointments):
    """
    Estimate probability (0-100) of landing another appointment in this area
    based on existing appointment density nearby on similar days.
    """
    # Look at all appointments within ~15 miles (0.22 deg) on same weekday
    weekday = target_date.weekday()
    nearby_count = 0
    total_days_checked = 0

    for rep_id, appts in all_appointments.items():
        days_seen = set()
        for a in appts:
            try:
                a_date = date.fromisoformat(a["date"])
            except Exception:
                continue
            if a_date.weekday() != weekday:
                continue
            if not a.get("lat") or not a.get("lng"):
                continue
            days_seen.add(a["date"])
            dist = haversine_drive_estimate(customer_lat, customer_lng, a["lat"], a["lng"])
            if dist <= 20:  # within ~20 min / ~15 miles
                nearby_count += 1
        total_days_checked += len(days_seen)

    if total_days_checked == 0:
        return 35  # baseline
    rate = nearby_count / total_days_checked
    prob = min(95, max(10, int(rate * 40 + 20)))
    return prob

def check_schedule_conflicts(reps, all_appointments, class_configs, scan_days=14):
    """
    Scan existing booked appointments for drive-time conflicts between consecutive
    appointments on the same day for each enabled rep.
    Returns list of issue dicts sorted by date then rep name.
    """
    issues = []
    today = date.today()

    for rep in reps:
        rep_class = rep.get("repClass", "")
        class_cfg = class_configs.get(rep_class, _DEFAULT_CLASS_CFG)
        max_days  = class_cfg.get("maxDaysOut", 7)
        window    = max(scan_days, max_days + 1)
        appt_dur  = rep.get("apptDurationMins", 45) / 60.0

        for day_offset in range(window):
            target_date = today + timedelta(days=day_offset)
            if target_date.weekday() >= 5:
                continue

            rep_appts = [a for a in all_appointments.get(rep["id"], [])
                         if a["date"] == target_date.isoformat()]
            rep_appts.sort(key=lambda a: a["startHour"])

            for i in range(len(rep_appts) - 1):
                a = rep_appts[i]
                b = rep_appts[i + 1]

                a_end          = a["startHour"] + appt_dur
                available_mins = (b["startHour"] - a_end) * 60

                # Get/cache coordinates for both appointments
                alat, alng = a.get("lat"), a.get("lng")
                if not alat and a.get("address"):
                    alat, alng = geocode_address(a["address"])
                    a["lat"], a["lng"] = alat, alng

                blat, blng = b.get("lat"), b.get("lng")
                if not blat and b.get("address"):
                    blat, blng = geocode_address(b["address"])
                    b["lat"], b["lng"] = blat, blng

                if not (alat and alng and blat and blng):
                    continue

                # Departure time = when rep leaves appointment A heading to appointment B
                a_end_dt   = datetime.combine(target_date, datetime.min.time()) + timedelta(hours=a["startHour"] + appt_dur)
                drive_mins = get_drive_time_minutes(alat, alng, blat, blng, a_end_dt)
                buffer     = available_mins - drive_mins

                if buffer < 0:
                    severity = "critical"
                elif buffer < 15:
                    severity = "warning"
                else:
                    continue  # no issue

                issues.append({
                    "severity":         severity,
                    "rep":              {"id": rep["id"], "name": rep["name"], "color": rep.get("color", "#6366f1")},
                    "date":             target_date.isoformat(),
                    "dayLabel":         format_day_label(target_date),
                    "apptA":            {"address": a.get("address", ""), "timeLabel": format_time(a["startHour"])},
                    "apptB":            {"address": b.get("address", ""), "timeLabel": format_time(b["startHour"])},
                    "driveMinutes":     int(drive_mins),
                    "availableMinutes": int(available_mins),
                    "bufferMinutes":    int(buffer),
                })

    issues.sort(key=lambda x: (x["date"], x["rep"]["name"]))
    return issues

def _drive_fast(olat, olng, dlat, dlng):
    """Drive time using cache if available, else Haversine — never blocks on Maps API."""
    coord_key = (round(olat, 3), round(olng, 3), round(dlat, 3), round(dlng, 3))
    cached = _drive_cache.get((coord_key, None))
    if cached is not None:
        return cached
    return haversine_drive_estimate(olat, olng, dlat, dlng)

def _rep_home_coords(rep):
    """Return (lat, lng) of rep's home/class origin, or (None, None)."""
    home = rep.get("homeAddress", "").strip()
    cls  = rep.get("repClass", "").strip().lower()
    origin = home or REP_CLASS_CITIES.get(cls, "")
    if origin:
        return geocode_address(origin)
    return None, None

def _base_legs(rep, sorted_appts):
    """
    Compute drive-time legs for one rep's day (home→a0, a0→a1, …).
    Uses cache-or-Haversine so it never blocks on a live Maps call.
    Returns list of per-leg minutes (same length as sorted_appts).
    """
    if not sorted_appts:
        return []
    legs = []
    hlat, hlng = _rep_home_coords(rep)
    first = sorted_appts[0]
    flat, flng = first.get("lat"), first.get("lng")
    if hlat and hlng and flat and flng:
        legs.append(_drive_fast(hlat, hlng, flat, flng))
    else:
        legs.append(45)  # unknown home — moderate default
    for i in range(len(sorted_appts) - 1):
        a = sorted_appts[i]
        b = sorted_appts[i + 1]
        alat, alng = a.get("lat"), a.get("lng")
        blat, blng = b.get("lat"), b.get("lng")
        legs.append(_drive_fast(alat, alng, blat, blng) if (alat and alng and blat and blng) else 0)
    return legs

def _insertion_feasible(sched, legs, insert_idx, appt_dur_hours):
    """
    Check that the appointment at insert_idx fits without creating a new drive conflict.
    Only checks the 1–2 gaps adjacent to the inserted appointment.
    """
    n = len(sched)
    if insert_idx > 0:
        gap = (sched[insert_idx]["startHour"] - sched[insert_idx - 1]["startHour"] - appt_dur_hours) * 60
        if legs[insert_idx] > gap:
            return False
    if insert_idx < n - 1:
        gap = (sched[insert_idx + 1]["startHour"] - sched[insert_idx]["startHour"] - appt_dur_hours) * 60
        if legs[insert_idx + 1] > gap:
            return False
    return True

def _build_sched(sorted_appts, legs, mark_idx=None, mark_type=None):
    """
    Build a display-ready schedule list.
    mark_type: "outgoing" (leaving this rep) or "incoming" (arriving from other rep).
    driveIn  = minutes to reach this appt (from home or previous appt).
    driveOut = minutes to the next appt (None for last).
    """
    items = []
    for k, appt in enumerate(sorted_appts):
        items.append({
            "timeLabel":    format_time(appt["startHour"]),
            "address":      appt.get("address", ""),
            "customerName": appt.get("customerName", ""),
            "markType":     mark_type if k == mark_idx else None,
            "driveIn":      int(legs[k]),
            "driveOut":     int(legs[k + 1]) if k < len(sorted_appts) - 1 else None,
        })
    return items

def _appt_label(appt):
    name = (appt.get("customerName") or "").strip()
    if name:
        return name
    return (appt.get("address") or "").split(",")[0].strip() or "Appt"

def _try_insert(rep, existing_appts, new_appt, appt_dur_hours):
    """
    Try inserting new_appt into rep's existing_appts (already sorted).
    Returns (feasible, new_sched, new_legs, insert_idx) or (False, None, None, None).
    """
    new_sched = sorted(existing_appts + [new_appt], key=lambda a: a["startHour"])
    new_legs  = _base_legs(rep, new_sched)
    idx       = next(k for k, a in enumerate(new_sched) if a is new_appt)
    if _insertion_feasible(new_sched, new_legs, idx, appt_dur_hours):
        return True, new_sched, new_legs, idx
    return False, None, None, None

def find_swap_suggestions(reps, all_appointments, scan_days=21, min_savings=15):
    """
    For each weekday, for every rep pair, find beneficial appointment reassignments:

    1. Bilateral swap  – Rep A takes B's appt (keeping B's time), Rep B takes A's appt
                         (keeping A's time). No customer's appointment time changes.
    2. Unilateral move – Rep A's appt moves to Rep B. No trade back. Saves ≥ min_savings.
    3. Time-adjusted   – Same as above but with ±30-min time shift. Saves ≥ 60 min.
                         These are clearly flagged because the customer's time changes.

    Uses cache-or-Haversine — never blocks on live Maps API.
    """
    suggestions = []
    seen = set()  # deduplicate by (date, appt_id_leaving, appt_id_arriving_or_None, shift)
    today = date.today()

    for day_offset in range(scan_days):
        target_date = today + timedelta(days=day_offset)
        if target_date.weekday() >= 5:
            continue
        date_str = target_date.isoformat()

        # Build per-rep schedule data (sorted appts with geocoded coords)
        day_schedules = {}
        for rep in reps:
            appts = [dict(a) for a in all_appointments.get(rep["id"], [])
                     if a["date"] == date_str]
            if not appts:
                continue
            for a in appts:
                if not a.get("lat") and a.get("address"):
                    a["lat"], a["lng"] = geocode_address(a["address"])
            appts = [a for a in appts if a.get("lat") and a.get("lng")]
            if not appts:
                continue
            appts.sort(key=lambda a: a["startHour"])
            legs = _base_legs(rep, appts)
            day_schedules[rep["id"]] = (rep, appts, legs, sum(legs))

        if len(day_schedules) < 2:
            continue

        rep_ids = list(day_schedules.keys())

        for i in range(len(rep_ids)):
            for j in range(i + 1, len(rep_ids)):
                rep_a, appts_a, legs_a, base_a = day_schedules[rep_ids[i]]
                rep_b, appts_b, legs_b, base_b = day_schedules[rep_ids[j]]
                base_total = base_a + base_b
                dur_a = rep_a.get("apptDurationMins", 45) / 60.0
                dur_b = rep_b.get("apptDurationMins", 45) / 60.0

                for appt_a in appts_a:
                    for appt_b in appts_b:

                        # ── 1. Bilateral swap ─────────────────────────────────────
                        # Rep A drops appt_a, picks up appt_b at appt_b's original time.
                        # Rep B drops appt_b, picks up appt_a at appt_a's original time.
                        # Customer appointment times are untouched.
                        rest_a = [a for a in appts_a if a is not appt_a]
                        rest_b = [a for a in appts_b if a is not appt_b]

                        ok_a, sched_a2, llegs_a2, idx_in_a = _try_insert(rep_a, rest_a, appt_b, dur_a)
                        ok_b, sched_b2, llegs_b2, idx_in_b = _try_insert(rep_b, rest_b, appt_a, dur_b)

                        if ok_a and ok_b:
                            new_a   = sum(llegs_a2)
                            new_b   = sum(llegs_b2)
                            savings = base_total - (new_a + new_b)
                            key     = (date_str, appt_a["id"], appt_b["id"], 0)
                            if savings >= min_savings and key not in seen:
                                seen.add(key)
                                orig_idx_a = appts_a.index(appt_a)
                                orig_idx_b = appts_b.index(appt_b)
                                lbl_a = _appt_label(appt_a)
                                lbl_b = _appt_label(appt_b)
                                suggestions.append({
                                    "type":          "swap",
                                    "description":   f"Move {lbl_a} ({format_time(appt_a['startHour'])}) to {rep_b['name']} and {lbl_b} ({format_time(appt_b['startHour'])}) to {rep_a['name']}",
                                    "date":          date_str,
                                    "dayLabel":      format_day_label(target_date),
                                    "repA":          {"id": rep_a["id"], "name": rep_a["name"], "color": rep_a.get("color","#6366f1")},
                                    "repB":          {"id": rep_b["id"], "name": rep_b["name"], "color": rep_b.get("color","#10b981")},
                                    "currentDriveA": int(base_a),
                                    "currentDriveB": int(base_b),
                                    "newDriveA":     int(new_a),
                                    "newDriveB":     int(new_b),
                                    "minutesSaved":  int(savings),
                                    "schedA":        _build_sched(appts_a, legs_a, orig_idx_a, "outgoing"),
                                    "schedAfterA":   _build_sched(sched_a2, llegs_a2, idx_in_a, "incoming"),
                                    "schedB":        _build_sched(appts_b, legs_b, orig_idx_b, "outgoing"),
                                    "schedAfterB":   _build_sched(sched_b2, llegs_b2, idx_in_b, "incoming"),
                                })

                        # ── 2. Unilateral move: A→B ──────────────────────────────
                        # Move appt_a from Rep A to Rep B (appt_b stays with B).
                        # Only worthwhile if A saves more than B costs.
                        ok_b2, sched_b3, llegs_b3, idx_in_b2 = _try_insert(rep_b, appts_b, appt_a, dur_b)
                        if ok_b2:
                            sched_a3  = [a for a in appts_a if a is not appt_a]
                            llegs_a3  = _base_legs(rep_a, sched_a3)
                            new_a3    = sum(llegs_a3)
                            new_b3    = sum(llegs_b3)
                            savings3  = base_total - (new_a3 + new_b3)
                            key3      = (date_str, appt_a["id"], None, 0)
                            if savings3 >= min_savings and key3 not in seen:
                                seen.add(key3)
                                orig_idx_a3 = appts_a.index(appt_a)
                                lbl_a3 = _appt_label(appt_a)
                                suggestions.append({
                                    "type":          "move",
                                    "description":   f"Move {lbl_a3} ({format_time(appt_a['startHour'])}) from {rep_a['name']} to {rep_b['name']}",
                                    "date":          date_str,
                                    "dayLabel":      format_day_label(target_date),
                                    "repA":          {"id": rep_a["id"], "name": rep_a["name"], "color": rep_a.get("color","#6366f1")},
                                    "repB":          {"id": rep_b["id"], "name": rep_b["name"], "color": rep_b.get("color","#10b981")},
                                    "currentDriveA": int(base_a),
                                    "currentDriveB": int(base_b),
                                    "newDriveA":     int(new_a3),
                                    "newDriveB":     int(new_b3),
                                    "minutesSaved":  int(savings3),
                                    "schedA":        _build_sched(appts_a, legs_a, orig_idx_a3, "outgoing"),
                                    "schedAfterA":   _build_sched(sched_a3, llegs_a3),
                                    "schedB":        _build_sched(appts_b, legs_b),
                                    "schedAfterB":   _build_sched(sched_b3, llegs_b3, idx_in_b2, "incoming"),
                                })

                        # ── 3. Time-adjusted moves (A→B, shift ±30 min) ──────────
                        # Customer's appointment time changes by 30 min. Only surface
                        # these when savings ≥ 60 min; flag clearly.
                        for shift in (-0.5, 0.5):
                            shifted_hour = appt_a["startHour"] + shift
                            if shifted_hour < 7 or shifted_hour > 19:
                                continue
                            appt_shifted = dict(appt_a)
                            appt_shifted["startHour"] = shifted_hour
                            ok_ta, sched_bta, llegs_bta, idx_bta = _try_insert(rep_b, appts_b, appt_shifted, dur_b)
                            if not ok_ta:
                                continue
                            sched_ata  = [a for a in appts_a if a is not appt_a]
                            llegs_ata  = _base_legs(rep_a, sched_ata)
                            new_ata    = sum(llegs_ata)
                            new_bta    = sum(llegs_bta)
                            savings_ta = base_total - (new_ata + new_bta)
                            key_ta     = (date_str, appt_a["id"], None, shift)
                            if savings_ta >= 60 and key_ta not in seen:
                                seen.add(key_ta)
                                shift_label = ("+30 min" if shift > 0 else "−30 min")
                                lbl_ta = _appt_label(appt_a)
                                old_t  = format_time(appt_a["startHour"])
                                new_t  = format_time(shifted_hour)
                                orig_idx_ta = appts_a.index(appt_a)
                                suggestions.append({
                                    "type":          "time-adjusted",
                                    "description":   f"Move {lbl_ta} (shift {old_t} → {new_t}) from {rep_a['name']} to {rep_b['name']}",
                                    "timeShift":     shift_label,
                                    "oldTime":       old_t,
                                    "newTime":       new_t,
                                    "date":          date_str,
                                    "dayLabel":      format_day_label(target_date),
                                    "repA":          {"id": rep_a["id"], "name": rep_a["name"], "color": rep_a.get("color","#6366f1")},
                                    "repB":          {"id": rep_b["id"], "name": rep_b["name"], "color": rep_b.get("color","#10b981")},
                                    "currentDriveA": int(base_a),
                                    "currentDriveB": int(base_b),
                                    "newDriveA":     int(new_ata),
                                    "newDriveB":     int(new_bta),
                                    "minutesSaved":  int(savings_ta),
                                    "schedA":        _build_sched(appts_a, legs_a, orig_idx_ta, "outgoing"),
                                    "schedAfterA":   _build_sched(sched_ata, llegs_ata),
                                    "schedB":        _build_sched(appts_b, legs_b),
                                    "schedAfterB":   _build_sched(sched_bta, llegs_bta, idx_bta, "incoming"),
                                })

    suggestions.sort(key=lambda s: -s["minutesSaved"])
    return suggestions[:30]

def format_day_label(d):
    today = date.today()
    if d == today:
        return "Today"
    if d == today + timedelta(days=1):
        return "Tomorrow"
    return d.strftime("%A, %b %d")

def format_time(hour):
    h    = int(hour)
    mins = int(round((hour % 1) * 60))
    ampm = "PM" if h >= 12 else "AM"
    h12  = h - 12 if h > 12 else (12 if h == 0 else h)
    return f"{h12}:{mins:02d} {ampm}"

# â"€â"€ HTTP handler â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€

class Handler(BaseHTTPRequestHandler):
    server_version = ""   # suppress "BaseHTTP/x.y" from error responses
    sys_version    = ""   # suppress "Python/3.x.y" from error responses

    def log_message(self, fmt, *args):
        pass  # suppress default access log

    def _cors_origin(self):
        origin = self.headers.get("Origin", "")
        return origin if origin in _ALLOWED_ORIGINS else "https://bam-scheduler.com"

    def _send_security_headers(self):
        origin = self._cors_origin()
        self.send_header("Access-Control-Allow-Origin",  origin)
        self.send_header("Access-Control-Allow-Headers", "Content-Type, X-Auth-Token")
        self.send_header("Vary",                         "Origin")
        self.send_header("X-Frame-Options",              "DENY")
        self.send_header("X-Content-Type-Options",       "nosniff")
        self.send_header("Referrer-Policy",              "no-referrer")
        self.send_header("Cache-Control",                "no-store")
        self.send_header("Permissions-Policy",           "geolocation=(), camera=(), microphone=()")
        self.send_header("Strict-Transport-Security",    "max-age=31536000; includeSubDomains")

    def _send_html_security_headers(self):
        """Additional headers for HTML document responses."""
        self._send_security_headers()
        # CSP: same-origin scripts only; allow Google Fonts/CDNs only if used (none here)
        self.send_header(
            "Content-Security-Policy",
            "default-src 'self'; "
            "script-src 'self' 'unsafe-inline'; "
            "style-src 'self' 'unsafe-inline'; "
            "img-src 'self' data:; "
            "connect-src 'self'; "
            "frame-ancestors 'none';"
        )

    def send_json(self, data, status=200):
        body = json.dumps(data).encode()
        self.send_response(status)
        self.send_header("Content-Type", "application/json")
        self._send_security_headers()
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def _token(self):
        return self.headers.get("X-Auth-Token", "")

    def _session(self):
        return _get_session(self._token())

    def _require_auth(self):
        """Returns session dict or sends 401 and returns None."""
        s = self._session()
        if not s:
            self.send_json({"error": "Unauthorized"}, 401)
        return s

    def _require_admin(self):
        """Returns session dict if admin, sends 403 and returns None otherwise."""
        s = self._require_auth()
        if s and s.get("role") != "admin":
            self.send_json({"error": "Forbidden"}, 403)
            return None
        return s

    def do_OPTIONS(self):
        self.send_response(200)
        self.send_header("Access-Control-Allow-Methods", "GET, POST, OPTIONS")
        self._send_security_headers()
        self.end_headers()

    def do_GET(self):
        parsed = urllib.parse.urlparse(self.path)
        path   = parsed.path
        params = dict(urllib.parse.parse_qsl(parsed.query))

        # â"€â"€ Auth: session info â"€â"€
        if path == "/api/me":
            s = self._session()
            if s:
                self.send_json({"username": s["username"], "role": s["role"]})
            else:
                self.send_json({"error": "Unauthorized"}, 401)
            return

        # Serve index.html (always â€" login screen is rendered by JS)
        if path in ("/", "/index.html"):
            html_path = os.path.join(os.path.dirname(__file__), "index.html")
            try:
                with open(html_path, "rb") as f:
                    body = f.read()
                self.send_response(200)
                self.send_header("Content-Type", "text/html; charset=utf-8")
                self._send_html_security_headers()
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)
            except FileNotFoundError:
                self.send_error(404, "index.html not found")
            return

        # ── Public health / geocode test (no auth required) ──
        if path == "/api/health":
            gb_lat, gb_lng = geocode_address("Green Bay, WI")
            sey_lat, sey_lng = geocode_address("Seymour, WI")
            self.send_json({
                "status": "ok",
                "googleMapsKeyPresent": bool(GMAPS_KEY),
                "geocodeGreenBay":  {"lat": gb_lat,  "lng": gb_lng,  "ok": gb_lat is not None},
                "geocodeSeymourWI": {"lat": sey_lat, "lng": sey_lng, "ok": sey_lat is not None},
            })
            return

        # All remaining API routes require a valid session
        if path.startswith("/api/") and not self._require_auth():
            return

        # â"€â"€ API: Places autocomplete (proxy â€" key stays server-side) â"€â"€
        if path == "/api/autocomplete":
            if _is_rate_limited(self._token(), "autocomplete", 60, 60):
                self.send_json({"error": "Too many requests"}, 429)
                return
            q = params.get("q", "").strip()
            if not q or not GMAPS_KEY:
                self.send_json({"suggestions": []})
                return
            try:
                ac_url = (
                    "https://maps.googleapis.com/maps/api/place/autocomplete/json"
                    f"?input={urllib.parse.quote(q)}&types=address&key={GMAPS_KEY}"
                )
                with urllib.request.urlopen(ac_url, timeout=5) as r:
                    data = json.loads(r.read())
                suggestions = [
                    {"description": p["description"], "placeId": p["place_id"]}
                    for p in data.get("predictions", [])
                ]
                self.send_json({"suggestions": suggestions})
            except Exception as e:
                print(f"[Maps] autocomplete error: {e}", flush=True)
                self.send_json({"suggestions": []})
            return

        # â"€â"€ API: Place details â†' lat/lng â"€â"€
        if path == "/api/place-details":
            if _is_rate_limited(self._token(), "place-details", 30, 60):
                self.send_json({"error": "Too many requests"}, 429)
                return
            place_id = params.get("placeId", "").strip()
            if not place_id or not GMAPS_KEY:
                self.send_json({"error": "missing"}, 400)
                return
            try:
                det_url = (
                    "https://maps.googleapis.com/maps/api/place/details/json"
                    f"?place_id={urllib.parse.quote(place_id)}"
                    f"&fields=formatted_address,geometry,address_components&key={GMAPS_KEY}"
                )
                with urllib.request.urlopen(det_url, timeout=5) as r:
                    data = json.loads(r.read())
                result = data.get("result", {})
                loc    = result.get("geometry", {}).get("location", {})
                addr   = result.get("formatted_address", "")
                lat    = loc.get("lat")
                lng    = loc.get("lng")
                # Extract city and state from address_components
                city, state = "", ""
                for comp in result.get("address_components", []):
                    types = comp.get("types", [])
                    if "locality" in types:
                        city = comp.get("long_name", "")
                    elif "administrative_area_level_1" in types:
                        state = comp.get("short_name", "")
                if addr and lat and lng:
                    _geocode_cache[addr] = (lat, lng)
                self.send_json({"address": addr, "lat": lat, "lng": lng,
                                "city": city, "state": state})
            except Exception as e:
                print(f"[Maps] place-details error: {e}", flush=True)
                self.send_json({"error": "Failed to retrieve place details"}, 500)
            return

        # -- API: city appointment probability --
        if path == "/api/reports/city-rate":
            city_q  = (params.get("city")  or "").strip().lower()
            state_q = (params.get("state") or "").strip().upper()
            if not city_q or not state_q:
                self.send_json({"error": "missing city/state"}, 400)
                return
            area = client_area({"city": city_q, "state": state_q}) or ""
            with _cache_lock:
                clients_snap = list(_client_cache)
            today    = date.today()
            start_ts = int(datetime(today.year, 1, 1).timestamp() * 1000)
            end_ts   = int(datetime.now().timestamp() * 1000)
            city_appts = 0
            area_appts = 0
            for c in clients_snap:
                if not is_demo_lead(c):
                    continue
                cd = c.get("createdDate")
                try:
                    cd_ms = float(cd or 0)
                except Exception:
                    cd_ms = 0
                if cd_ms <= MIGRATION_CUTOFF_TS:
                    continue
                if not (start_ts <= cd_ms <= end_ts):
                    continue
                c_area = client_area(c)
                if c_area != area:
                    continue
                area_appts += 1
                c_city  = (c.get("city")  or "").strip().lower()
                c_state = (c.get("state") or "").strip().upper()
                if c_city == city_q and c_state == state_q:
                    city_appts += 1
            prob = round(city_appts / area_appts * 100, 1) if area_appts > 0 else None
            self.send_json({
                "city":       params.get("city", ""),
                "state":      state_q,
                "area":       area,
                "cityAppts":  city_appts,
                "areaAppts":  area_appts,
                "probability": prob,
                "year":       today.year,
            })
            return

        # â"€â"€ API: search contacts â"€â"€
        if path == "/api/contacts/search":
            q = params.get("q", "").lower().strip()
            if len(q) < 2:
                self.send_json({"contacts": []})
                return
            if DEMO_MODE or not BP_API_KEY:
                results = [c for c in MOCK_CONTACTS if
                           q in c["firstName"].lower() or
                           q in c["lastName"].lower() or
                           q in c.get("address","").lower() or
                           q in c.get("phone","")]
            else:
                results = search_clients_bp(q) or []
            self.send_json({"contacts": results})
            return

        # â"€â"€ API: get reps â"€â"€
        if path == "/api/reps":
            if DEMO_MODE or not BP_API_KEY:
                self.send_json({"reps": MOCK_REPS})
            else:
                reps = get_cached_reps() or MOCK_REPS
                self.send_json({"reps": reps})
            return

        # â"€â"€ API: schedule options â"€â"€
        if path == "/api/schedule-options":
            if _is_rate_limited(self._token(), "schedule-options", 20, 60):
                self.send_json({"error": "Too many requests"}, 429)
                return
            customer_id = params.get("customerId")
            cust_lat = params.get("lat")
            cust_lng = params.get("lng")

            # Look up customer
            contact = None
            if DEMO_MODE or not BP_API_KEY:
                contact = next((c for c in MOCK_CONTACTS if c["id"] == customer_id), None)
            else:
                contact = get_client_bp(customer_id)
                # BP doesn't support single-client GET; fall back to params passed by frontend
                if not contact and params.get("firstName"):
                    contact = {
                        "id":        customer_id,
                        "firstName": params.get("firstName", ""),
                        "lastName":  params.get("lastName", ""),
                        "phone":     params.get("phone", ""),
                        "email":     params.get("email", ""),
                        "address":   params.get("address", ""),
                        "lat":       None,
                        "lng":       None,
                    }

            if not contact:
                self.send_json({"error": "Customer not found"}, 404)
                return

            lat = float(cust_lat) if cust_lat else contact.get("lat")
            lng = float(cust_lng) if cust_lng else contact.get("lng")

            # Geocode if no coords
            if not lat and contact.get("address") and GMAPS_KEY:
                lat, lng = geocode_address(contact["address"])

            if not lat or not lng:
                # Fallback coords (centre of Dallas metro)
                lat, lng = 32.89, -96.76

            # Load reps
            if DEMO_MODE or not BP_API_KEY:
                reps = MOCK_REPS
                all_appointments = MOCK_APPOINTMENTS
            else:
                reps = get_cached_reps() or MOCK_REPS
                sched_cfg  = load_sched_config()
                max_window = max((v.get("maxDaysOut", 7) for v in sched_cfg.values()), default=7)
                end_str    = (date.today() + timedelta(days=max_window + 1)).isoformat()
                all_appointments = get_cached_appointments(date.today().isoformat(), end_str)

            # Apply admin rep config (enabled flag + priority percentage + home address + class)
            rep_cfg = load_rep_config()
            for rep in reps:
                cfg = rep_cfg.get(rep["id"], {})
                rep["priority_pct"]     = cfg.get("priority", 50)
                rep["homeAddress"]      = cfg.get("homeAddress", "")
                rep["repClass"]         = cfg.get("repClass", "")
                rep["apptDurationMins"] = cfg.get("apptDurationMins", 45)
            reps = [r for r in reps if rep_cfg.get(r["id"], {}).get("enabled", True)]

            class_configs = load_sched_config()
            result = find_schedule_options(lat, lng, reps, all_appointments,
                                           class_configs=class_configs)
            self.send_json({
                "customer":     contact,
                "options":      result["options"],
                "extraOptions": result["extraOptions"],
                "customerLat":  lat,
                "customerLng":  lng,
            })
            return

        # â"€â"€ API: user list (admin only) â"€â"€
        if path == "/api/admin/users":
            if not self._require_admin():
                return
            users = load_users()
            self.send_json({"users": [
                {"username": u, "role": d["role"]} for u, d in users.items()
            ]})
            return

        # â"€â"€ API: admin rep config â"€â"€
        if path == "/api/admin/reps":
            if not self._require_admin():
                return
            all_reps = MOCK_REPS if (DEMO_MODE or not BP_API_KEY) else (get_cached_reps() or MOCK_REPS)
            cfg = load_rep_config()
            result = []
            for r in all_reps:
                c = cfg.get(r["id"], {})
                result.append({**r,
                    "enabled":          c.get("enabled", True),
                    "priority_pct":     c.get("priority", 50),
                    "repClass":         c.get("repClass", ""),
                    "homeAddress":      c.get("homeAddress", ""),
                    "apptDurationMins": c.get("apptDurationMins", 45),
                })
            self.send_json({"reps": result})
            return

        # â"€â"€ API: scheduling / class config â"€â"€
        if path == "/api/admin/classes":
            if not self._require_admin():
                return
            self.send_json({"classes": load_sched_config()})
            return

        # â"€â"€ API: conflict scan â"€â"€
        if path == "/api/conflicts":
            if DEMO_MODE or not BP_API_KEY:
                self.send_json({"issues": []})
                return
            reps = get_cached_reps() or []
            rep_cfg = load_rep_config()
            for rep in reps:
                c = rep_cfg.get(rep["id"], {})
                rep["repClass"]         = c.get("repClass", "")
                rep["homeAddress"]      = c.get("homeAddress", "")
                rep["apptDurationMins"] = c.get("apptDurationMins", 45)
            reps = [r for r in reps if rep_cfg.get(r["id"], {}).get("enabled", True)]
            sched_cfg  = load_sched_config()
            max_window = max((v.get("maxDaysOut", 7) for v in sched_cfg.values()), default=7)
            end_str    = (date.today() + timedelta(days=max(14, max_window + 1))).isoformat()
            all_appts  = get_all_appointments_bp(date.today().isoformat(), end_str) or {}
            issues     = check_schedule_conflicts(reps, all_appts, sched_cfg)
            self.send_json({"issues": issues})
            return

        # ── API: schedule optimizer (admin only) ──
        if path == "/api/schedule-optimizer":
            if not self._require_admin():
                return
            if DEMO_MODE or not BP_API_KEY:
                self.send_json({"suggestions": []})
                return
            reps = get_cached_reps() or []
            rep_cfg = load_rep_config()
            for rep in reps:
                c = rep_cfg.get(rep["id"], {})
                rep["repClass"]         = c.get("repClass", "")
                rep["homeAddress"]      = c.get("homeAddress", "")
                rep["apptDurationMins"] = c.get("apptDurationMins", 45)
            reps = [r for r in reps if rep_cfg.get(r["id"], {}).get("enabled", True)]
            end_str   = (date.today() + timedelta(days=22)).isoformat()
            all_appts = get_all_appointments_bp(date.today().isoformat(), end_str) or {}
            suggestions = find_swap_suggestions(reps, all_appts, scan_days=21)
            self.send_json({"suggestions": suggestions})
            return

        # ── API: config/status (admin only) ──
        if path == "/api/status":
            if not self._require_admin():
                return
            self.send_json({
                "demoMode": DEMO_MODE,
                "builderPrimeConnected": bool(BP_API_KEY),
                "googleMapsConnected": bool(GMAPS_KEY),
            })
            return

        # â"€â"€ API: close-rate report â"€â"€
        # ── API: scheduling diagnostics (admin only) ──
        if path == "/api/debug-schedule":
            if not self._require_admin():
                return
            rep_cfg = load_rep_config()
            sched_cfg = load_sched_config()
            reps = get_cached_reps() or []
            for rep in reps:
                cfg = rep_cfg.get(rep["id"], {})
                rep["homeAddress"]  = cfg.get("homeAddress", "")
                rep["repClass"]     = cfg.get("repClass", "")
                rep["priority_pct"] = cfg.get("priority", 50)
                rep["enabled"]      = cfg.get("enabled", True)
            test_lat, test_lng = 44.5062582, -88.3332937  # Seymour WI
            rep_debug = []
            for rep in reps:
                home = rep.get("homeAddress", "").strip()
                cls  = rep.get("repClass", "").strip().lower()
                city = REP_CLASS_CITIES.get(cls, "")
                hlat, hlng = geocode_address(home) if home else (None, None)
                city_lat, city_lng = geocode_address(city) if city else (None, None)
                drive = None
                if hlat and hlng:
                    drive = get_drive_time_minutes(hlat, hlng, test_lat, test_lng)
                elif city_lat and city_lng:
                    drive = get_drive_time_minutes(city_lat, city_lng, test_lat, test_lng)
                rep_debug.append({
                    "id": rep["id"], "name": rep.get("name",""),
                    "enabled": rep.get("enabled", True),
                    "repClass": rep.get("repClass",""),
                    "homeAddress": home,
                    "homeGeocoded": hlat is not None,
                    "homeLat": hlat, "homeLng": hlng,
                    "classCityFallback": city,
                    "classCityGeocoded": city_lat is not None,
                    "driveToSeymourWI": drive,
                })
            test_addr = "740 Woodside Drive Seymour, WI 54165"
            test_result = geocode_address(test_addr)
            now = datetime.now()
            self.send_json({
                "serverTimeUTC": now.isoformat(),
                "repCount": len(reps),
                "schedClasses": list(sched_cfg.keys()),
                "googleMapsKeyPresent": bool(GMAPS_KEY),
                "testGeocode": {"address": test_addr, "result": list(test_result)},
                "geocodeCacheSize": len(_geocode_cache),
                "reps": rep_debug,
            })
            return

        if path == "/api/reports/close-rates":
            if not self._require_admin():
                return

            today     = date.today()
            start_str = params.get("start", f"{today.year}-01-01")
            end_str   = params.get("end",   today.isoformat())
            try:
                start_ts = int(datetime(*[int(x) for x in start_str.split("-")]).timestamp() * 1000)
                end_ts   = int(datetime(*[int(x) for x in end_str.split("-")], 23, 59, 59).timestamp() * 1000)
            except Exception:
                start_ts = int(datetime(today.year, 1, 1).timestamp() * 1000)
                end_ts   = int(datetime.now().timestamp() * 1000)

            with _cache_lock:
                clients_snap = list(_client_cache)

            from collections import Counter
            city_agg   = {}   # "City, ST" -> [total, sold, area]
            status_dbg = Counter()
            skipped_migration = 0

            for c in clients_snap:
                if not is_demo_lead(c):
                    continue

                # Use createdDate for date filtering.
                # Clients with createdDate <= MIGRATION_CUTOFF_TS have an unreliable
                # June-2024 migration date â€" exclude them from date-filtered reports.
                cd = c.get("createdDate")
                try:
                    cd_ms = float(cd or 0)
                except Exception:
                    cd_ms = 0

                if cd_ms <= MIGRATION_CUTOFF_TS:
                    skipped_migration += 1
                    continue
                if not (start_ts <= cd_ms <= end_ts):
                    continue

                area = client_area(c)
                if not area:
                    continue

                city  = (c.get("city")  or "").strip() or "Unknown"
                state = (c.get("state") or "").strip().upper() or "??"
                key   = f"{city}, {state}"

                sold = is_sold_client(c)
                if key not in city_agg:
                    city_agg[key] = [0, 0, area]
                city_agg[key][0] += 1
                if sold:
                    city_agg[key][1] += 1
                status_dbg[(c.get("leadStatusName") or "").strip()] += 1

            total_all  = sum(v[0] for v in city_agg.values())
            total_sold = sum(v[1] for v in city_agg.values())
            print(f"[Report] {start_str} to {end_str} total={total_all} sold={total_sold} "
                  f"skipped_migration={skipped_migration} cache={len(clients_snap)}", flush=True)

            _AREA_ORDER = {"Iowa": 0, "Ft Worth": 1, "Green Bay": 2, "Milwaukee": 3}

            def make_row(label, vals):
                total, sold_cnt, area_label = vals
                return {"label": label, "total": total, "sold": sold_cnt,
                        "area": area_label,
                        "rate": round(sold_cnt / total * 100, 1) if total > 0 else 0}

            self.send_json({
                "totalLeads":  total_all,
                "totalSold":   total_sold,
                "overallRate": round(total_sold / total_all * 100, 1) if total_all > 0 else 0,
                "dateRange":   {"start": start_str, "end": end_str},
                "cacheSize":   len(clients_snap),
                "byArea":      sorted(
                    [make_row(k, v) for k, v in city_agg.items()],
                    key=lambda x: (_AREA_ORDER.get(x["area"], 99), -x["total"])
                ),
                "statusBreakdown": status_dbg.most_common(30),
            })
            return

        self.send_error(404, "Not found")

    def do_POST(self):
        parsed = urllib.parse.urlparse(self.path)
        length = int(self.headers.get("Content-Length", 0))
        if length > 1_048_576:  # 1 MB cap
            self.send_json({"error": "Request too large"}, 413)
            return
        body = {}
        if length:
            try:
                body = json.loads(self.rfile.read(length).decode())
            except Exception:
                pass

        # â"€â"€ Auth: login â"€â"€
        if parsed.path == "/api/login":
            username = body.get("username", "").strip()
            password = body.get("password", "")
            locked, secs = _is_login_locked(username)
            if locked:
                mins = secs // 60 + 1
                self.send_json({"error": f"Too many failed attempts. Try again in {mins} minute(s)."}, 429)
                return
            users = load_users()
            u = users.get(username)
            if u and _verify_password(password, u["passwordHash"]):
                _clear_login_attempts(username)
                token = _create_session(username, u["role"])
                print(f"[Auth] Login: {username} ({u['role']})", flush=True)
                self.send_json({"token": token, "username": username, "role": u["role"]})
            else:
                _record_login_fail(username)
                print(f"[Auth] Failed login for '{username}'", flush=True)
                self.send_json({"error": "Invalid username or password"}, 401)
            return

        # â"€â"€ Auth: logout â"€â"€
        if parsed.path == "/api/logout":
            _invalidate_session(self.headers.get("X-Auth-Token", ""))
            self.send_json({"ok": True})
            return

        # â"€â"€ Auth: change own password â"€â"€
        if parsed.path == "/api/change-password":
            s = self._require_auth()
            if not s:
                return
            current  = body.get("current", "")
            new_pw   = body.get("new", "")
            if not new_pw or len(new_pw) < 8:
                self.send_json({"error": "Password must be at least 8 characters"}, 400)
                return
            users = load_users()
            u = users.get(s["username"])
            if not u or not _verify_password(current, u["passwordHash"]):
                self.send_json({"error": "Current password is incorrect"}, 403)
                return
            users[s["username"]]["passwordHash"] = _hash_password(new_pw)
            save_users(users)
            print(f"[Auth] Password changed: {s['username']}", flush=True)
            self.send_json({"ok": True})
            return

        # â"€â"€ Auth: admin user management â"€â"€
        if parsed.path == "/api/admin/users":
            if not self._require_admin():
                return
            action   = body.get("action")
            username = body.get("username", "").strip()
            if not username:
                self.send_json({"error": "Username required"}, 400)
                return
            users = load_users()
            if action == "create":
                if username in users:
                    self.send_json({"error": "User already exists"}, 400)
                    return
                role = body.get("role", "user")
                pw   = body.get("password", "")
                if not pw or len(pw) < 4:
                    self.send_json({"error": "Password must be at least 8 characters"}, 400)
                    return
                users[username] = {"passwordHash": _hash_password(pw), "role": role}
                save_users(users)
                self.send_json({"ok": True})
            elif action == "delete":
                if username == self._session()["username"]:
                    self.send_json({"error": "Cannot delete your own account"}, 400)
                    return
                users.pop(username, None)
                save_users(users)
                self.send_json({"ok": True})
            elif action == "set-password":
                if username not in users:
                    self.send_json({"error": "User not found"}, 404)
                    return
                pw = body.get("password", "")
                if not pw or len(pw) < 4:
                    self.send_json({"error": "Password must be at least 8 characters"}, 400)
                    return
                users[username]["passwordHash"] = _hash_password(pw)
                save_users(users)
                self.send_json({"ok": True})
            elif action == "set-role":
                if username not in users:
                    self.send_json({"error": "User not found"}, 404)
                    return
                users[username]["role"] = body.get("role", "user")
                save_users(users)
                self.send_json({"ok": True})
            else:
                self.send_json({"error": "Unknown action"}, 400)
            return

        # All remaining POST routes require auth
        if not self._require_auth():
            return

        if parsed.path == "/api/admin/reps":
            if not self._require_admin():
                return
            try:
                reps_dict = body.get("reps", {})
                save_rep_config(reps_dict)
                print(f"[Admin] Saved config for {len(reps_dict)} reps to {REP_CONFIG_FILE}", flush=True)
                self.send_json({"ok": True})
            except Exception as e:
                print(f"[Admin] Rep config save failed: {e}", flush=True)
                self.send_json({"ok": False, "error": "Failed to save rep config"}, 500)
            return

        if parsed.path == "/api/admin/classes":
            if not self._require_admin():
                return
            try:
                save_sched_config(body.get("classes", {}))
                self.send_json({"ok": True})
            except Exception as e:
                print(f"[Admin] Class config save failed: {e}", flush=True)
                self.send_json({"ok": False, "error": "Failed to save class config"}, 500)
            return

        self.send_error(404)


# â"€â"€ Entry point â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€

if __name__ == "__main__":
    _init_users()
    threading.Thread(target=_cache_refresh_loop, daemon=True).start()
    threading.Thread(target=_warmup_caches, daemon=True).start()
    threading.Thread(target=_cleanup_sessions, daemon=True).start()
    threading.Thread(target=_cleanup_rate_limits, daemon=True).start()
    server = ThreadedHTTPServer(("0.0.0.0", PORT), Handler)
    mode_str = "DEMO MODE" if DEMO_MODE else "LIVE MODE"
    bp_status   = "Connected" if BP_API_KEY else "Not set (using mock data)"
    maps_status = "Connected" if GMAPS_KEY  else "Not set (using estimates)"
    print(f"Call Center Scheduler [{mode_str}] on http://localhost:{PORT}", flush=True)
    print(f"  Builder Prime API: {bp_status}", flush=True)
    print(f"  Google Maps API:   {maps_status}", flush=True)
    server.serve_forever()


