"""
SkyFly Flight Reservation System
================================
A desktop application built with Python's standard library only (tkinter).
No external packages are required. Data is stored in skyfly_data.json.

Booking flow
------------
  1. Passenger      - personal, contact, ID and special-assistance details
  2. Flight Search  - From, To, date; Economy / Premium / Business fares side by side
  3. Meals          - meal preference (Veg, Jain, Diabetic ...) and optional food (or Skip)
  4. Baggage        - smart baggage calculator (extra charges calculated automatically)
  5. Seat           - Smart Seat Recommendation + interactive seat map
  6. Payment        - UPI ID / method, loyalty-points redemption (simulated payment)
  7. Confirmation   - "Booking Successful" screen, e-ticket and QR boarding pass

Smart features
--------------
  * Dynamic ticket pricing        - fare depends on days to departure and seats filled
  * Waitlist + auto-confirmation  - full flights can be waitlisted; the first waitlisted
                                    passenger gets a seat automatically when someone cancels
  * QR-code boarding pass         - QR generated in pure Python (no libraries)
  * Flight delay prediction       - Naive Bayes model trained on sample historical data
  * Smart baggage calculator      - allowance by cabin class, excess / cabin / special items
  * Meal preference booking       - Vegetarian, Non-Veg, Jain, Vegan, Diabetic, Gluten-free
  * Emergency-exit seat rule      - age / special-assistance eligibility check
  * Price comparison              - all three cabin classes shown together
  * Loyalty points                - earn on every booking, redeem at payment
  * Carbon-emission estimate      - CO2 per passenger for the selected journey
  * Smart Seat Recommendation    - "Window + Front" -> "Recommended Seat: 4A"

"Manage Booking" (top right): look up a PNR, view the ticket, boarding pass, or cancel.
"Loyalty Points" (top right): check a points balance by mobile number.

Run:  python skyfly_flight_reservation_system.py
"""

import json
import math
import os
import random
import re
import tkinter as tk
from datetime import date, datetime, time, timedelta
from tkinter import filedialog, messagebox, ttk
from xml.sax.saxutils import escape as xml_escape

# --------------------------------------------------------------- constants
APP_NAME = "SkyFly Flight Reservation System"
DATA_FILE = "skyfly_data.json"
DT_FMT = "%Y-%m-%d %H:%M"
GST_RATE = 0.05
CLASS_MULTIPLIER = {"Economy": 1.0, "Premium Economy": 1.4, "Business": 2.2}
CLASS_PERKS = {
    "Economy": "15 kg check-in  |  7 kg cabin",
    "Premium Economy": "20 kg check-in  |  priority boarding",
    "Business": "30 kg check-in  |  lounge  |  priority boarding",
}
MONTHS = ["Jan", "Feb", "Mar", "Apr", "May", "Jun",
          "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"]

C = {
    "primary": "#0B3D91", "primary_dark": "#082B66", "accent": "#F59E0B",
    "bg": "#F3F6FB", "text": "#1F2937", "muted": "#6B7280", "ok": "#15803D",
    "avail": "#DCE7FA", "taken": "#9CA3AF", "border": "#C9D3E6",
    "legroom": "#FDE68A", "reco": "#F97316", "restricted": "#FCA5A5", "warn": "#B45309",
}

# flight no, origin, destination, dep hour, dep minute, duration (min), base fare, seats
ROUTES = [
    ("SF101", "Hyderabad", "Delhi", 6, 0, 150, 5200, 60),
    ("SF102", "Delhi", "Hyderabad", 9, 30, 150, 5100, 60),
    ("SF201", "Hyderabad", "Mumbai", 9, 15, 90, 3100, 48),
    ("SF202", "Mumbai", "Hyderabad", 13, 0, 90, 3000, 48),
    ("SF301", "Delhi", "Bengaluru", 14, 0, 165, 4800, 48),
    ("SF302", "Bengaluru", "Delhi", 18, 45, 165, 4900, 48),
    ("SF401", "Mumbai", "Chennai", 18, 30, 110, 3600, 42),
    ("SF402", "Chennai", "Hyderabad", 8, 0, 75, 2800, 36),
    ("SF501", "Hyderabad", "Bengaluru", 11, 0, 80, 2600, 36),
    ("SF502", "Bengaluru", "Hyderabad", 16, 30, 80, 2650, 36),
]

CITY_COORDS = {  # latitude, longitude (for distance / CO2 estimate)
    "Hyderabad": (17.385, 78.4867), "Delhi": (28.6139, 77.2090),
    "Mumbai": (19.0760, 72.8777), "Bengaluru": (12.9716, 77.5946),
    "Chennai": (13.0827, 80.2707),
}

# Meal menu: id, category, item name, price (Rs), vegetarian?, tags
MENU = [
    ("v1", "Veg Meals", "Paneer Butter Masala with Jeera Rice", 280, True, ("dairy", "onion")),
    ("v2", "Veg Meals", "Veg Biryani with Raita", 250, True, ("dairy", "onion")),
    ("v3", "Veg Meals", "Veg Club Sandwich", 160, True, ("gluten", "dairy")),
    ("n1", "Non-Veg Meals", "Chicken Biryani with Raita", 320, False, ("dairy", "onion")),
    ("n2", "Non-Veg Meals", "Butter Chicken with Rice", 340, False, ("dairy", "onion")),
    ("n3", "Non-Veg Meals", "Egg Sandwich", 150, False, ("gluten", "egg", "onion")),
    ("s1", "Snacks & Desserts", "Samosa (2 pcs) with Chutney", 90, True, ("gluten", "onion")),
    ("s2", "Snacks & Desserts", "Chocolate Brownie", 120, True, ("gluten", "sugar", "dairy")),
    ("s3", "Snacks & Desserts", "Gulab Jamun (2 pcs)", 90, True, ("gluten", "sugar", "dairy")),
    ("b1", "Beverages", "Tea / Coffee", 70, True, ("dairy", "sugar")),
    ("b2", "Beverages", "Fresh Orange Juice", 110, True, ("sugar",)),
    ("b3", "Beverages", "Soft Drink (Can)", 90, True, ("sugar",)),
    ("b4", "Beverages", "Packaged Drinking Water", 30, True, ()),
]
MAX_QTY = 3  # per item

# meal preference -> (vegetarian only?, banned tags)
PREF_RULES = {
    "No preference": (False, ()),
    "Vegetarian": (True, ()),
    "Non-Vegetarian": (False, ()),
    "Jain": (True, ("onion",)),
    "Vegan": (True, ("dairy", "egg")),
    "Diabetic (low sugar)": (False, ("sugar",)),
    "Gluten-free": (False, ("gluten",)),
}

# baggage rules
BAGGAGE_ALLOWANCE = {"Economy": 15.0, "Premium Economy": 20.0, "Business": 30.0}  # check-in kg
CABIN_LIMIT = 7.0
CABIN_MAX = 10.0
MAX_CHECKIN_KG = 40.0
MAX_BAG_KG = 32.0
RATE_FIRST_5KG = 350   # Rs per kg for the first 5 kg over the allowance
RATE_BEYOND = 550      # Rs per kg beyond that
RATE_CABIN = 350       # Rs per kg over the cabin limit
SPECIAL_ITEMS = {"None": 0, "Sports equipment": 1500, "Musical instrument": 1200}

# loyalty
POINTS_PER_RS = 100      # 1 point per Rs. 100 paid
MAX_REDEEM_PCT = 0.5     # points can pay for at most 50% of the bill (1 point = Re. 1)

# carbon estimate
CO2_KG_PER_PAX_KM = 0.115
CLASS_CO2_FACTOR = {"Economy": 1.0, "Premium Economy": 1.5, "Business": 2.0}
TREE_KG_PER_YEAR = 21.0

ASSIST_OPTIONS = ["None", "Wheelchair / reduced mobility", "Visual or hearing impairment"]


# ------------------------------------------------------------- persistence
def ensure_flights(db, days=30):
    """Add any missing daily flights for the next `days` days."""
    existing = {f["id"] for f in db["flights"]}
    today = date.today()
    for d in range(days):
        day = today + timedelta(days=d)
        for no, origin, dest, hh, mm, dur, price, seats in ROUTES:
            fid = f"{no}-{day:%Y%m%d}"
            if fid in existing:
                continue
            dep = datetime.combine(day, time(hh, mm))
            db["flights"].append({
                "id": fid, "no": no, "origin": origin, "dest": dest,
                "dep": dep.strftime(DT_FMT),
                "arr": (dep + timedelta(minutes=dur)).strftime(DT_FMT),
                "price": price, "seats": seats})


def save_db(db):
    with open(DATA_FILE, "w", encoding="utf-8") as fh:
        json.dump(db, fh, indent=2)


def load_db():
    db = {"flights": [], "bookings": [], "loyalty": {}}
    if os.path.exists(DATA_FILE):
        try:
            with open(DATA_FILE, "r", encoding="utf-8") as fh:
                db = json.load(fh)
        except (json.JSONDecodeError, OSError):
            os.replace(DATA_FILE, DATA_FILE + ".bak")  # keep the damaged file
            db = {"flights": [], "bookings": [], "loyalty": {}}
    db.setdefault("flights", [])
    db.setdefault("bookings", [])
    db.setdefault("loyalty", {})
    ensure_flights(db)
    save_db(db)
    return db


# ----------------------------------------------------------------- helpers
def money(x):
    return f"Rs. {x:,.2f}"


def valid_email(s):
    return re.fullmatch(r"[^@\s]+@[^@\s]+\.[^@\s]+", s) is not None


def valid_phone(s):
    return s.isdigit() and len(s) == 10


def valid_upi(s):
    return re.fullmatch(r"[A-Za-z0-9._\-]{2,64}@[A-Za-z][A-Za-z0-9]{1,31}", s) is not None


def mask_upi(upi):
    user, _, bank = upi.partition("@")
    return f"{user[:2]}{'*' * max(len(user) - 2, 3)}@{bank}"


def calc_age(dob, today=None):
    today = today or date.today()
    return today.year - dob.year - ((today.month, today.day) < (dob.month, dob.day))


def duration_text(dep, arr):
    mins = int((datetime.strptime(arr, DT_FMT) - datetime.strptime(dep, DT_FMT)).total_seconds() // 60)
    return f"{mins // 60}h {mins % 60:02d}m"


# ---- dynamic pricing ------------------------------------------------------
def dynamic_factor(flight, taken, now=None):
    """Demand-based price multiplier from days-to-departure and seats filled.
    Returns (factor, [reasons])."""
    now = now or datetime.now()
    dep = datetime.strptime(flight["dep"], DT_FMT)
    days = (dep - now).total_seconds() / 86400
    if days >= 30:
        t, why_t = 0.90, "early-bird discount (30+ days ahead)"
    elif days >= 15:
        t, why_t = 1.00, "standard advance purchase"
    elif days >= 7:
        t, why_t = 1.15, "departs within 2 weeks"
    elif days >= 3:
        t, why_t = 1.30, "departs within a week"
    else:
        t, why_t = 1.50, "last-minute booking"
    load = taken / max(flight["seats"], 1)
    if load >= 0.9:
        o, why_o = 1.40, f"almost full ({load:.0%} booked)"
    elif load >= 0.7:
        o, why_o = 1.25, f"filling fast ({load:.0%} booked)"
    elif load >= 0.4:
        o, why_o = 1.10, f"moderate demand ({load:.0%} booked)"
    else:
        o, why_o = 1.00, f"plenty of seats ({load:.0%} booked)"
    return round(t * o, 2), [why_t, why_o]


# ---- baggage calculator ---------------------------------------------------
def baggage_charge(cls, checkin_kg, cabin_kg, special):
    allowance = BAGGAGE_ALLOWANCE[cls]
    excess = max(0.0, checkin_kg - allowance)
    first = min(excess, 5.0)
    rest = max(0.0, excess - 5.0)
    checkin_fee = first * RATE_FIRST_5KG + rest * RATE_BEYOND
    cabin_excess = max(0.0, cabin_kg - CABIN_LIMIT)
    cabin_fee = cabin_excess * RATE_CABIN
    special_fee = SPECIAL_ITEMS.get(special, 0)
    return {"allowance": allowance, "excess": excess, "first": first, "rest": rest,
            "checkin_fee": checkin_fee, "cabin_excess": cabin_excess, "cabin_fee": cabin_fee,
            "special": special, "special_fee": special_fee,
            "total": round(checkin_fee + cabin_fee + special_fee, 2)}


# ---- meal preference ------------------------------------------------------
def meal_allowed(item, pref):
    veg_only, banned = PREF_RULES[pref]
    _iid, _cat, _name, _price, veg, tags = item
    if veg_only and not veg:
        return False
    return not any(t in tags for t in banned)


# ---- seats ----------------------------------------------------------------
def seat_labels(n):
    return [f"{i // 6 + 1}{'ABCDEF'[i % 6]}" for i in range(n)]


def seat_rows(flight):
    return -(-flight["seats"] // 6)


def exit_rows(total_rows):
    if total_rows < 4:
        return set()
    mid = total_rows // 2
    return {mid, mid + 1}


def seat_info(label, flight):
    row, letter = int(label[:-1]), label[-1]
    rows = seat_rows(flight)
    exit_row = row in exit_rows(rows)
    legroom = exit_row or row == 1
    position = {"A": "Window", "F": "Window", "C": "Aisle", "D": "Aisle"}.get(letter, "Middle")
    third = -(-rows // 3)
    zone = "Front" if row <= third else ("Middle" if row <= 2 * third else "Back")
    fee = 500 if legroom else (200 if zone == "Front" else 0)
    fee += 100 if position == "Window" else (50 if position == "Aisle" else 0)
    return {"row": row, "letter": letter, "position": position, "zone": zone,
            "exit": exit_row, "legroom": legroom, "fee": fee}


def exit_eligibility(p):
    """Emergency-exit rows are only for able, adult passengers."""
    age = p.get("age", 0)
    if age < 15:
        return False, "passengers under 15 years cannot sit in emergency-exit rows"
    if age > 65:
        return False, "passengers over 65 years are not allocated emergency-exit rows"
    if p.get("assist", "None") != "None":
        return False, "passengers needing special assistance cannot sit in emergency-exit rows"
    return True, ""


def recommend_seat(flight, taken, exit_ok, prefs):
    """Pick the best free seat for the stated preferences."""
    labels = seat_labels(flight["seats"])
    meta = {l: seat_info(l, flight) for l in labels}
    avail = {l for l in labels if l not in taken and (exit_ok or not meta[l]["exit"])}
    if not avail:
        return None
    pos = prefs.get("position", "No preference")
    zone = prefs.get("zone", "No preference")
    want_leg = prefs.get("legroom", False)
    group = prefs.get("family", 0)
    cheapest = prefs.get("cheapest", False)
    max_fee = max(m["fee"] for m in meta.values()) or 1

    def run_with(label):
        row, letter = meta[label]["row"], label[-1]
        side = "ABC" if letter in "ABC" else "DEF"
        idx = side.index(letter)
        lo = hi = idx
        while lo > 0 and f"{row}{side[lo - 1]}" in avail:
            lo -= 1
        while hi < 2 and f"{row}{side[hi + 1]}" in avail:
            hi += 1
        return [f"{row}{side[i]}" for i in range(lo, hi + 1)]

    family_ok = group < 2 or any(len(run_with(l)) >= group for l in avail)
    if not family_ok:
        group = 0  # no row has enough seats together: fall back to the best single seat
    if pos == "No preference" and zone == "No preference" and not want_leg and group < 2:
        cheapest = True  # nothing to match: suggest the best-value seat

    best = None
    for l in sorted(avail, key=lambda x: (meta[x]["row"], x[-1])):
        m = meta[l]
        score = -0.5 * m["fee"] / max_fee  # tie-breaker: prefer the cheaper of equally good seats
        if pos != "No preference" and m["position"] == pos:
            score += 3
        if zone != "No preference" and m["zone"] == zone:
            score += 3
        if want_leg and m["legroom"]:
            score += 4
        if cheapest:
            score += 4 * (1 - m["fee"] / max_fee)
        run = run_with(l)
        if group >= 2:
            score += 5 if len(run) >= group else -5
        if best is None or score > best[0] + 1e-9:
            best = (score, l, run)
    _score, label, run = best
    companions = []
    if group >= 2:
        companions = sorted((s for s in run if s != label),
                            key=lambda s: abs(run.index(s) - run.index(label)))[:group - 1]
        companions.sort()
    return {"label": label, "meta": meta[label], "companions": companions, "family_ok": family_ok}


# ---- carbon estimate ------------------------------------------------------
def distance_km(a, b):
    if a not in CITY_COORDS or b not in CITY_COORDS:
        return None
    (la1, lo1), (la2, lo2) = CITY_COORDS[a], CITY_COORDS[b]
    p1, p2 = math.radians(la1), math.radians(la2)
    dphi, dl = p2 - p1, math.radians(lo2 - lo1)
    h = math.sin(dphi / 2) ** 2 + math.cos(p1) * math.cos(p2) * math.sin(dl / 2) ** 2
    return 2 * 6371.0 * math.asin(math.sqrt(h))


def co2_estimate(origin, dest, cls):
    """Approximate kg CO2 per passenger (great-circle distance +5% routing)."""
    d = distance_km(origin, dest)
    if d is None:
        return None
    return round(d * 1.05 * CO2_KG_PER_PAX_KM * CLASS_CO2_FACTOR[cls], 1)


# ---- delay prediction (Naive Bayes on sample historical data) -------------
def delay_band(hour):
    if hour < 9:
        return "early"
    if hour < 12:
        return "morning"
    if hour < 17:
        return "afternoon"
    return "evening"


def season_of(month):
    if 6 <= month <= 9:
        return "monsoon"
    if month in (12, 1, 2):
        return "winter"
    return "other"


def sample_history(n=1800, seed=7):
    """Synthetic 'historical' records: (origin, hour, month, weekday, delayed, minutes)."""
    rng = random.Random(seed)
    rows = []
    for _ in range(n):
        origin = rng.choice(list(CITY_COORDS))
        hour, month, weekday = rng.randint(5, 22), rng.randint(1, 12), rng.randint(0, 6)
        p = 0.10
        if 17 <= hour <= 21:
            p += 0.15
        elif hour <= 8:
            p -= 0.03
        if 6 <= month <= 9:
            p += 0.12
        if origin == "Delhi" and month in (12, 1):
            p += 0.20
        if origin == "Mumbai" and 6 <= month <= 9:
            p += 0.08
        if weekday >= 5:
            p += 0.04
        delayed = rng.random() < p
        minutes = rng.randint(16, 150) if delayed else rng.randint(0, 12)
        rows.append((origin, hour, month, weekday, delayed, minutes))
    return rows


class DelayModel:
    """Categorical Naive Bayes with Laplace smoothing: P(delay | origin, time band, season, day type)."""

    def __init__(self, rows=None):
        rows = rows if rows is not None else sample_history()
        self.cls_count = {True: 0, False: 0}
        self.feat_count = {True: {}, False: {}}
        self.vocab = {}
        self.delay_minutes = {}
        for origin, hour, month, weekday, delayed, minutes in rows:
            self.cls_count[delayed] += 1
            for feat in self.features(origin, hour, month, weekday):
                self.feat_count[delayed][feat] = self.feat_count[delayed].get(feat, 0) + 1
                self.vocab.setdefault(feat[0], set()).add(feat[1])
            if delayed:
                self.delay_minutes.setdefault(delay_band(hour), []).append(minutes)

    @staticmethod
    def features(origin, hour, month, weekday):
        return (("origin", origin), ("band", delay_band(hour)), ("season", season_of(month)),
                ("day", "weekend" if weekday >= 5 else "weekday"))

    def predict(self, origin, dep):
        total = sum(self.cls_count.values())
        logp = {}
        for c in (True, False):
            lp = math.log(self.cls_count[c] / total)
            for feat in self.features(origin, dep.hour, dep.month, dep.weekday()):
                cnt = self.feat_count[c].get(feat, 0)
                lp += math.log((cnt + 1) / (self.cls_count[c] + len(self.vocab[feat[0]])))
            logp[c] = lp
        m = max(logp.values())
        e = {c: math.exp(v - m) for c, v in logp.items()}
        prob = e[True] / (e[True] + e[False])
        label = "Low" if prob < 0.20 else ("Medium" if prob < 0.35 else "High")
        mins = self.delay_minutes.get(delay_band(dep.hour)) or [30]
        return {"prob": round(prob, 3), "label": label, "avg_min": int(sum(mins) / len(mins))}


# ---- QR code generator (byte mode, ECC level M, versions 1-10) ------------
_QR_ECC_PER_BLOCK = [0, 10, 16, 26, 18, 24, 16, 18, 22, 22, 26]
_QR_NUM_BLOCKS = [0, 1, 1, 1, 2, 2, 4, 4, 4, 5, 5]


def _qr_raw_modules(ver):
    result = (16 * ver + 128) * ver + 64
    if ver >= 2:
        n = ver // 7 + 2
        result -= (25 * n - 10) * n - 55
        if ver >= 7:
            result -= 36
    return result


def _qr_data_codewords(ver):
    return _qr_raw_modules(ver) // 8 - _QR_ECC_PER_BLOCK[ver] * _QR_NUM_BLOCKS[ver]


def _gf_mul(x, y):
    z = 0
    for i in reversed(range(8)):
        z = (z << 1) ^ ((z >> 7) * 0x11D)
        z ^= ((y >> i) & 1) * x
    return z


def _rs_divisor(degree):
    result = [0] * (degree - 1) + [1]
    root = 1
    for _ in range(degree):
        for j in range(degree):
            result[j] = _gf_mul(result[j], root)
            if j + 1 < degree:
                result[j] ^= result[j + 1]
        root = _gf_mul(root, 2)
    return result


def _rs_remainder(data, divisor):
    result = [0] * len(divisor)
    for b in data:
        factor = b ^ result.pop(0)
        result.append(0)
        for i, coef in enumerate(divisor):
            result[i] ^= _gf_mul(coef, factor)
    return result


def _qr_encode_data(data, ver):
    bits = []

    def append(val, n):
        bits.extend((val >> i) & 1 for i in reversed(range(n)))

    append(0b0100, 4)
    append(len(data), 8 if ver < 10 else 16)
    for b in data:
        append(b, 8)
    cap_bits = _qr_data_codewords(ver) * 8
    append(0, min(4, cap_bits - len(bits)))
    append(0, -len(bits) % 8)
    pad = 0xEC
    while len(bits) < cap_bits:
        append(pad, 8)
        pad ^= 0xEC ^ 0x11
    return [int("".join(map(str, bits[i:i + 8])), 2) for i in range(0, len(bits), 8)]


def _qr_add_ecc(data, ver):
    nb, ecc_len = _QR_NUM_BLOCKS[ver], _QR_ECC_PER_BLOCK[ver]
    raw = _qr_raw_modules(ver) // 8
    num_short, short_len = nb - raw % nb, raw // nb
    divisor = _rs_divisor(ecc_len)
    blocks, k = [], 0
    for i in range(nb):
        dat = data[k:k + short_len - ecc_len + (0 if i < num_short else 1)]
        k += len(dat)
        ecc = _rs_remainder(dat, divisor)
        if i < num_short:
            dat = dat + [0]
        blocks.append(dat + ecc)
    result = []
    for i in range(len(blocks[0])):
        for j, blk in enumerate(blocks):
            if i != short_len - ecc_len or j >= num_short:
                result.append(blk[i])
    return result


def _qr_align_positions(ver):
    if ver == 1:
        return []
    size = ver * 4 + 17
    n = ver // 7 + 2
    step = (ver * 4 + n * 2 + 1) // (n * 2 - 2) * 2
    return ([size - 7 - i * step for i in range(n - 1)] + [6])[::-1]


def _qr_draw_format(modules, func, size, mask):
    data = 0 << 3 | mask  # ECC level M has format bits 00
    rem = data
    for _ in range(10):
        rem = (rem << 1) ^ ((rem >> 9) * 0x537)
    bits = (data << 10 | rem) ^ 0x5412

    def put(x, y, i):
        modules[y][x] = ((bits >> i) & 1) != 0
        func[y][x] = True

    for i in range(0, 6):
        put(8, i, i)
    put(8, 7, 6)
    put(8, 8, 7)
    put(7, 8, 8)
    for i in range(9, 15):
        put(14 - i, 8, i)
    for i in range(0, 8):
        put(size - 1 - i, 8, i)
    for i in range(8, 15):
        put(8, size - 15 + i, i)
    modules[size - 8][8] = True
    func[size - 8][8] = True


def _qr_mask_bit(mask, x, y):
    return [(x + y) % 2 == 0, y % 2 == 0, x % 3 == 0, (x + y) % 3 == 0,
            (x // 3 + y // 2) % 2 == 0, x * y % 2 + x * y % 3 == 0,
            (x * y % 2 + x * y % 3) % 2 == 0, ((x + y) % 2 + x * y % 3) % 2 == 0][mask]


def _qr_penalty(m):
    size = len(m)
    result = 0
    lines = [row for row in m] + [[m[y][x] for y in range(size)] for x in range(size)]
    for line in lines:
        run = 1
        for i in range(1, size):
            if line[i] == line[i - 1]:
                run += 1
            else:
                if run >= 5:
                    result += 3 + run - 5
                run = 1
        if run >= 5:
            result += 3 + run - 5
        s = "".join("1" if v else "0" for v in line)
        for pat in ("10111010000", "00001011101"):
            start = s.find(pat)
            while start != -1:
                result += 40
                start = s.find(pat, start + 1)
    for y in range(size - 1):
        for x in range(size - 1):
            if m[y][x] == m[y][x + 1] == m[y + 1][x] == m[y + 1][x + 1]:
                result += 3
    dark = sum(v for row in m for v in row)
    total = size * size
    k = -(-abs(dark * 20 - total * 10) // total) - 1
    return result + max(k, 0) * 10


def make_qr(text):
    """Return a square matrix (list of lists of bool, True = dark module) encoding `text`."""
    data = text.encode("utf-8")
    for ver in range(1, 11):
        if 4 + (8 if ver < 10 else 16) + 8 * len(data) <= _qr_data_codewords(ver) * 8:
            break
    else:
        raise ValueError("Text is too long for the QR code generator.")
    size = ver * 4 + 17
    codewords = _qr_add_ecc(_qr_encode_data(data, ver), ver)

    modules = [[False] * size for _ in range(size)]
    func = [[False] * size for _ in range(size)]

    def set_func(x, y, dark):
        modules[y][x] = dark
        func[y][x] = True

    for i in range(size):
        set_func(6, i, i % 2 == 0)
        set_func(i, 6, i % 2 == 0)
    for cx, cy in ((3, 3), (size - 4, 3), (3, size - 4)):
        for dy in range(-4, 5):
            for dx in range(-4, 5):
                x, y = cx + dx, cy + dy
                if 0 <= x < size and 0 <= y < size:
                    set_func(x, y, max(abs(dx), abs(dy)) not in (2, 4))
    pos = _qr_align_positions(ver)
    n = len(pos)
    for i in range(n):
        for j in range(n):
            if (i == 0 and j == 0) or (i == 0 and j == n - 1) or (i == n - 1 and j == 0):
                continue
            for dy in range(-2, 3):
                for dx in range(-2, 3):
                    set_func(pos[i] + dx, pos[j] + dy, max(abs(dx), abs(dy)) != 1)
    _qr_draw_format(modules, func, size, 0)  # reserve format areas
    if ver >= 7:
        rem = ver
        for _ in range(12):
            rem = (rem << 1) ^ ((rem >> 11) * 0x1F25)
        bits = ver << 12 | rem
        for i in range(18):
            bit = ((bits >> i) & 1) != 0
            a, b = size - 11 + i % 3, i // 3
            set_func(a, b, bit)
            set_func(b, a, bit)

    i = 0
    for right in range(size - 1, 0, -2):
        if right <= 6:
            right -= 1
        for vert in range(size):
            for j in range(2):
                x = right - j
                upward = (right + 1) & 2 == 0
                y = (size - 1 - vert) if upward else vert
                if not func[y][x] and i < len(codewords) * 8:
                    modules[y][x] = ((codewords[i >> 3] >> (7 - (i & 7))) & 1) != 0
                    i += 1

    best, best_pen = None, None
    for mask in range(8):
        m = [row[:] for row in modules]
        for y in range(size):
            for x in range(size):
                if not func[y][x] and _qr_mask_bit(mask, x, y):
                    m[y][x] = not m[y][x]
        _qr_draw_format(m, [row[:] for row in func], size, mask)
        pen = _qr_penalty(m)
        if best_pen is None or pen < best_pen:
            best, best_pen = m, pen
    return best


class DatePicker(ttk.Frame):
    """Day / Month / Year drop-downs (tkinter has no built-in calendar)."""

    def __init__(self, parent, years):
        super().__init__(parent)
        self.day = ttk.Combobox(self, values=[f"{i:02d}" for i in range(1, 32)], width=4, state="readonly")
        self.month = ttk.Combobox(self, values=MONTHS, width=5, state="readonly")
        self.year = ttk.Combobox(self, values=[str(y) for y in years], width=6, state="readonly")
        for w in (self.day, self.month, self.year):
            w.pack(side="left", padx=(0, 4))

    def set(self, d):
        self.day.set(f"{d.day:02d}")
        self.month.set(MONTHS[d.month - 1])
        self.year.set(str(d.year))

    def get(self):
        if not (self.day.get() and self.month.get() and self.year.get()):
            raise ValueError("Select a complete date.")
        return date(int(self.year.get()), MONTHS.index(self.month.get()) + 1, int(self.day.get()))


# --------------------------------------------------------------- application
class SkyFlyApp(tk.Tk):
    STEP_TITLES = ["Passenger", "Flight Search", "Meals", "Baggage", "Seat", "Payment", "Confirmation"]

    def __init__(self):
        super().__init__()
        self.title(APP_NAME)
        self.geometry("1180x780")
        self.minsize(1100, 720)
        self.configure(bg=C["bg"])
        self.db = load_db()
        self.delay_model = DelayModel()
        self.reset_state()
        self.setup_style()
        self.build_shell()
        self.show_step(0)
        self.center_window(self)

    # -------------------------------------------------------------- setup
    def reset_state(self):
        self.step = 0
        self.passenger = {}
        self.search = {}
        self.row_info = {}
        self.flight = None
        self.cls = "Economy"
        self.dyn_factor = 1.0
        self.dyn_reasons = []
        self.waitlist = False
        self.meal_pref = "No preference"
        self.meal_qty = {}
        self.bag = {"bags": 1, "checkin": 0.0, "cabin": 0.0, "special": "None"}
        self.seat = None
        self.recommended = None
        self.payment_method = "UPI"
        self.upi_id = ""
        self.points_used = 0
        self.last_booking = None

    def setup_style(self):
        s = ttk.Style(self)
        s.theme_use("clam")
        bg = C["bg"]
        s.configure(".", background=bg, foreground=C["text"], font=("Segoe UI", 10))
        s.configure("TFrame", background=bg)
        s.configure("TLabel", background=bg, foreground=C["text"])
        s.configure("TCheckbutton", background=bg)
        s.configure("TRadiobutton", background=bg, font=("Segoe UI", 10, "bold"))
        s.configure("TLabelframe", background=bg, bordercolor=C["border"])
        s.configure("TLabelframe.Label", background=bg, foreground=C["primary"], font=("Segoe UI", 10, "bold"))
        s.configure("Title.TLabel", font=("Segoe UI", 16, "bold"), foreground=C["primary"])
        s.configure("Muted.TLabel", foreground=C["muted"])
        s.configure("Bold.TLabel", font=("Segoe UI", 10, "bold"))
        s.configure("Total.TLabel", font=("Segoe UI", 12, "bold"), foreground=C["primary"])
        s.configure("TButton", padding=(14, 7))
        s.configure("Primary.TButton", background=C["primary"], foreground="white",
                    font=("Segoe UI", 10, "bold"), padding=(18, 8))
        s.map("Primary.TButton", background=[("active", C["primary_dark"]), ("disabled", C["taken"])])
        s.configure("Accent.TButton", background=C["accent"], foreground=C["text"],
                    font=("Segoe UI", 10, "bold"))
        s.map("Accent.TButton", background=[("active", "#D98A06")])
        s.configure("Treeview", rowheight=28, fieldbackground="white", font=("Segoe UI", 10))
        s.configure("Treeview.Heading", background=C["primary"], foreground="white",
                    font=("Segoe UI", 10, "bold"), padding=6)
        s.map("Treeview.Heading", background=[("active", C["primary_dark"])])
        s.map("Treeview", background=[("selected", C["accent"])], foreground=[("selected", C["text"])])

    def build_shell(self):
        header = tk.Frame(self, bg=C["primary"])
        header.pack(fill="x")
        tk.Label(header, text="\u2708  SkyFly", font=("Segoe UI", 22, "bold"),
                 fg="white", bg=C["primary"]).pack(side="left", padx=(20, 10), pady=12)
        tk.Label(header, text="Flight Reservation System", font=("Segoe UI", 13),
                 fg="#BFD3F5", bg=C["primary"]).pack(side="left")
        ttk.Button(header, text="Manage Booking", style="Accent.TButton",
                   command=self.open_manage).pack(side="right", padx=(6, 20))
        ttk.Button(header, text="Loyalty Points", style="Accent.TButton",
                   command=self.open_loyalty).pack(side="right", padx=6)

        self.stepbar = tk.Frame(self, bg="white", highlightbackground=C["border"], highlightthickness=1)
        self.stepbar.pack(fill="x")
        self.step_labels = []
        for _ in self.STEP_TITLES:
            lbl = tk.Label(self.stepbar, font=("Segoe UI", 10, "bold"), pady=9, bg="white")
            lbl.pack(side="left", expand=True, fill="x")
            self.step_labels.append(lbl)

        self.footer = ttk.Frame(self)
        self.footer.pack(side="bottom", fill="x", padx=20, pady=12)
        self.footer.columnconfigure(1, weight=1)
        self.back_btn = ttk.Button(self.footer, text="\u2039  Back", command=self.on_back)
        self.next_btn = ttk.Button(self.footer, text="Continue  \u203a", style="Primary.TButton",
                                   command=self.on_next)
        self.back_btn.grid(row=0, column=0)
        self.next_btn.grid(row=0, column=2)

        self.body = ttk.Frame(self)
        self.body.pack(fill="both", expand=True, padx=24, pady=(10, 0))

    def center_window(self, win, over=None):
        win.update_idletasks()
        w, h = win.winfo_width(), win.winfo_height()
        if over is not None:
            x = over.winfo_x() + (over.winfo_width() - w) // 2
            y = over.winfo_y() + (over.winfo_height() - h) // 2
        else:
            x = (win.winfo_screenwidth() - w) // 2
            y = (win.winfo_screenheight() - h) // 3
        win.geometry(f"+{max(x, 0)}+{max(y, 0)}")

    # --------------------------------------------------------- navigation
    def show_step(self, i):
        self.step = i
        for w in self.body.winfo_children():
            w.destroy()
        [self.build_passenger, self.build_search, self.build_meals, self.build_baggage,
         self.build_seat, self.build_payment, self.build_confirm][i]()
        self.update_stepbar()
        if i == 0:
            self.back_btn.grid_remove()
        else:
            self.back_btn.grid()
        if i == 6:
            self.back_btn.grid_remove()
            self.next_btn.grid_remove()
        else:
            self.next_btn.grid()
            text = {0: "Continue  \u203a", 1: "Continue  \u203a", 2: "Add Meals & Continue  \u203a",
                    3: "Continue to Seats  \u203a", 4: "Continue to Payment  \u203a",
                    5: "Pay & Join Waitlist" if self.waitlist else "Pay & Confirm"}[i]
            self.next_btn.config(text=text)

    def update_stepbar(self):
        for n, lbl in enumerate(self.step_labels):
            title = self.STEP_TITLES[n]
            if n < self.step:
                lbl.config(text=f"\u2714  {title}", fg=C["ok"], bg="white")
            elif n == self.step:
                lbl.config(text=f"{n + 1}.  {title}", fg=C["text"], bg=C["accent"])
            else:
                lbl.config(text=f"{n + 1}.  {title}", fg=C["muted"], bg="white")

    def on_back(self):
        if self.step > 0:
            self.show_step(self.step - 1)

    def on_next(self):
        handlers = [self.collect_passenger, self.collect_search, self.collect_meals,
                    self.collect_baggage, self.collect_seat, self.collect_payment]
        if handlers[self.step]() and self.step < 5:
            self.show_step(self.step + 1)

    def warn(self, text, widget=None):
        messagebox.showwarning("SkyFly", text, parent=self)
        if widget is not None:
            try:
                widget.focus_set()
            except tk.TclError:
                pass
        return False

    def heading(self, title, subtitle=""):
        ttk.Label(self.body, text=title, style="Title.TLabel").pack(anchor="w")
        if subtitle:
            ttk.Label(self.body, text=subtitle, style="Muted.TLabel").pack(anchor="w", pady=(0, 6))

    # ---------------------------------------------------- data look-ups
    def find_flight(self, fid):
        return next((f for f in self.db["flights"] if f["id"] == fid), None)

    def taken_seats(self, fid):
        return {b["seat"] for b in self.db["bookings"]
                if b["flight_id"] == fid and b["status"] == "CONFIRMED" and b.get("seat")}

    def seats_left(self, f):
        return f["seats"] - len(self.taken_seats(f["id"]))

    def cities(self):
        return sorted({f["origin"] for f in self.db["flights"]} | {f["dest"] for f in self.db["flights"]})

    def new_pnr(self):
        chars = "ABCDEFGHJKLMNPQRSTUVWXYZ23456789"
        used = {b["pnr"] for b in self.db["bookings"]}
        while True:
            pnr = "SF" + "".join(random.choice(chars) for _ in range(6))
            if pnr not in used:
                return pnr

    def delay_for(self, flight):
        return self.delay_model.predict(flight["origin"], datetime.strptime(flight["dep"], DT_FMT))

    def waitlist_position(self, b):
        pos = 0
        for x in self.db["bookings"]:
            if x["flight_id"] == b["flight_id"] and x["status"] == "WAITLISTED":
                pos += 1
                if x["pnr"] == b["pnr"]:
                    return pos
        return 0

    # --------------------------------------------------------- loyalty
    def loyalty_account(self, key):
        return self.db["loyalty"].setdefault(key, {"points": 0, "history": []})

    def loyalty_balance(self, key):
        return self.db["loyalty"].get(key, {}).get("points", 0)

    def add_points(self, key, pts, note):
        acct = self.loyalty_account(key)
        acct["points"] = max(0, acct["points"] + pts)
        acct["history"].append({"date": datetime.now().strftime(DT_FMT), "points": pts, "note": note})
        acct["history"] = acct["history"][-50:]

    # --------------------------------------------------------- pricing
    def meals_list(self):
        out = []
        for iid, _cat, name, price, _veg, _tags in MENU:
            q = self.meal_qty.get(iid, 0)
            if q > 0:
                out.append({"id": iid, "name": name, "qty": q, "price": price})
        return out

    def meals_total(self):
        return round(sum(m["qty"] * m["price"] for m in self.meals_list()), 2)

    def bag_info(self):
        return baggage_charge(self.cls, self.bag["checkin"], self.bag["cabin"], self.bag["special"])

    def seat_fee(self):
        if self.waitlist or not self.seat:
            return 0
        return seat_info(self.seat, self.flight)["fee"]

    def pricing(self):
        price = round(self.flight["price"] * CLASS_MULTIPLIER[self.cls] * self.dyn_factor, 2)
        meals, bag, seat = self.meals_total(), self.bag_info()["total"], float(self.seat_fee())
        gst = round((price + meals + bag + seat) * GST_RATE, 2)
        gross = round(price + meals + bag + seat + gst, 2)
        discount = float(min(self.points_used, int(gross * MAX_REDEEM_PCT)))
        return {"price": price, "meals": meals, "bag": bag, "seat": seat, "gst": gst,
                "gross": gross, "discount": discount, "total": round(gross - discount, 2)}

    # ===================================================== STEP 1: PASSENGER
    def build_passenger(self):
        self.heading("Passenger Details",
                     "Enter the traveller's details exactly as they appear on the ID proof.  (* required)")
        p = self.passenger
        self.pw = {}
        today = date.today()
        dob_years = list(range(today.year, today.year - 101, -1))
        sections = [
            ("Personal Information", [
                ("title", "Title", "combo", ["Mr", "Ms", "Mrs", "Dr"]),
                ("full_name", "Full name", "entry", None),
                ("dob", "Date of birth", "date", dob_years),
                ("gender", "Gender", "combo", ["Male", "Female", "Other"]),
                ("nationality", "Nationality", "entry", "Indian"),
                ("assist", "Special assistance", "combo", ASSIST_OPTIONS),
            ]),
            ("Contact Information", [
                ("email", "Email address", "entry", None),
                ("phone", "Mobile number (10 digits)", "entry", None),
                ("address", "Address", "entry", None),
                ("city", "City", "entry", None),
            ]),
            ("Identification", [
                ("id_type", "ID proof type", "combo",
                 ["Aadhaar", "Passport", "Driving Licence", "Voter ID", "PAN Card"]),
                ("id_number", "ID number", "entry", None),
            ]),
        ]
        for title, spec in sections:
            box = ttk.LabelFrame(self.body, text=title, padding=(14, 8))
            box.pack(fill="x", pady=5)
            for idx, (key, label, kind, opts) in enumerate(spec):
                r, c = divmod(idx, 2)
                c *= 2
                ttk.Label(box, text=f"{label} *").grid(row=r, column=c, sticky="w", padx=(0, 10), pady=5)
                if kind == "combo":
                    w = ttk.Combobox(box, values=opts, state="readonly", width=26)
                    w.set(p.get(key, opts[0]))
                elif kind == "date":
                    w = DatePicker(box, opts)
                    if p.get("dob"):
                        w.set(date.fromisoformat(p["dob"]))
                else:
                    w = ttk.Entry(box, width=29)
                    w.insert(0, p.get(key, opts if isinstance(opts, str) else ""))
                w.grid(row=r, column=c + 1, sticky="w", padx=(0, 30), pady=5)
                self.pw[key] = w
        ttk.Label(self.body, style="Muted.TLabel",
                  text="Special assistance and age decide whether emergency-exit seats can be offered. "
                       "Your mobile number is your loyalty-points account.").pack(anchor="w", pady=4)

    def collect_passenger(self):
        w = self.pw
        name = w["full_name"].get().strip()
        if not re.fullmatch(r"[A-Za-z][A-Za-z .'\-]{1,59}", name):
            return self.warn("Enter a valid full name (letters only).", w["full_name"])
        try:
            dob = w["dob"].get()
        except ValueError:
            return self.warn("Select a valid date of birth.", w["dob"].day)
        if dob >= date.today():
            return self.warn("Date of birth must be in the past.", w["dob"].day)
        age = calc_age(dob)
        if age > 120:
            return self.warn("Please check the date of birth.", w["dob"].day)
        nationality = w["nationality"].get().strip()
        if not nationality:
            return self.warn("Enter the nationality.", w["nationality"])
        email = w["email"].get().strip()
        if not valid_email(email):
            return self.warn("Enter a valid email address.", w["email"])
        phone = w["phone"].get().strip()
        if not valid_phone(phone):
            return self.warn("Mobile number must be exactly 10 digits.", w["phone"])
        address = w["address"].get().strip()
        if len(address) < 5:
            return self.warn("Enter the full address.", w["address"])
        city = w["city"].get().strip()
        if not city:
            return self.warn("Enter the city.", w["city"])
        id_number = w["id_number"].get().strip().replace(" ", "")
        if not (6 <= len(id_number) <= 20 and id_number.isalnum()):
            return self.warn("Enter a valid ID number (6-20 letters/digits).", w["id_number"])
        self.passenger = {
            "title": w["title"].get(), "full_name": name, "dob": dob.isoformat(), "age": age,
            "gender": w["gender"].get(), "nationality": nationality, "assist": w["assist"].get(),
            "email": email, "phone": phone, "address": address, "city": city,
            "id_type": w["id_type"].get(), "id_number": id_number,
        }
        return True

    # ======================================================= STEP 2: SEARCH
    def build_search(self):
        self.heading("Search Flights", "Choose where you are flying from and to, and your travel date. "
                                       "Fares for all cabins are shown together.")
        s = self.search
        cities = self.cities()
        box = ttk.LabelFrame(self.body, text="Journey", padding=(14, 8))
        box.pack(fill="x", pady=4)
        ttk.Label(box, text="From").grid(row=0, column=0, sticky="w")
        self.s_from = ttk.Combobox(box, values=cities, state="readonly", width=16)
        self.s_from.grid(row=1, column=0, padx=(0, 16), pady=(2, 0))
        ttk.Label(box, text="To").grid(row=0, column=1, sticky="w")
        self.s_to = ttk.Combobox(box, values=cities, state="readonly", width=16)
        self.s_to.grid(row=1, column=1, padx=(0, 16), pady=(2, 0))
        ttk.Label(box, text="Travel date").grid(row=0, column=2, sticky="w")
        today = date.today()
        self.s_date = DatePicker(box, sorted({today.year, (today + timedelta(days=30)).year}))
        self.s_date.grid(row=1, column=2, padx=(0, 16), pady=(2, 0))
        ttk.Button(box, text="Search Flights", style="Primary.TButton",
                   command=self.run_search).grid(row=1, column=3, padx=8)
        if s:
            self.s_from.set(s["origin"])
            self.s_to.set(s["dest"])
            self.s_date.set(date.fromisoformat(s["date"]))
        else:
            self.s_date.set(today + timedelta(days=1))

        self.s_status = ttk.Label(self.body, text="Select From, To and Date, then press Search Flights.",
                                  style="Muted.TLabel")
        self.s_status.pack(anchor="w", pady=(6, 3))

        cols = ("Flight", "Departure", "Arrival", "Duration", "Economy", "Premium Eco.",
                "Business", "Seats left", "Delay risk")
        widths = (70, 140, 140, 80, 105, 115, 105, 90, 130)
        frame = ttk.Frame(self.body)
        frame.pack(fill="both", expand=True)
        self.s_tree = ttk.Treeview(frame, columns=cols, show="headings", selectmode="browse", height=6)
        for c, wd in zip(cols, widths):
            self.s_tree.heading(c, text=c)
            self.s_tree.column(c, width=wd, anchor="w")
        self.s_tree.tag_configure("full", foreground=C["warn"])
        sb = ttk.Scrollbar(frame, orient="vertical", command=self.s_tree.yview)
        self.s_tree.configure(yscrollcommand=sb.set)
        self.s_tree.pack(side="left", fill="both", expand=True)
        sb.pack(side="right", fill="y")

        cmp_box = ttk.LabelFrame(self.body, text="Compare fares and choose your cabin", padding=(14, 8))
        cmp_box.pack(fill="x", pady=(8, 0))
        self.cls_var = tk.StringVar(value=self.cls)
        self.fare_labels = {}
        for i, name in enumerate(CLASS_MULTIPLIER):
            ttk.Radiobutton(cmp_box, text=name, variable=self.cls_var, value=name).grid(
                row=0, column=i, sticky="w", padx=(0, 40))
            lbl = ttk.Label(cmp_box, text="-", style="Total.TLabel")
            lbl.grid(row=1, column=i, sticky="w")
            ttk.Label(cmp_box, text=CLASS_PERKS[name], style="Muted.TLabel").grid(
                row=2, column=i, sticky="w", padx=(0, 40))
            self.fare_labels[name] = lbl
        self.s_dyn = ttk.Label(cmp_box, text="", style="Muted.TLabel")
        self.s_dyn.grid(row=3, column=0, columnspan=3, sticky="w", pady=(6, 0))
        self.s_tree.bind("<<TreeviewSelect>>", lambda e: self.update_fare_cards())

        if s:
            self.run_search(silent=True)
            if self.flight and self.s_tree.exists(self.flight["id"]):
                self.s_tree.selection_set(self.flight["id"])
                self.update_fare_cards()

    def update_fare_cards(self):
        sel = self.s_tree.selection()
        info = self.row_info.get(sel[0]) if sel else None
        for name, lbl in self.fare_labels.items():
            lbl.config(text=f"{money(info['prices'][name])} + GST" if info else "-")
        if info:
            self.s_dyn.config(text=f"Dynamic pricing x{info['factor']:.2f}: " + "; ".join(info["reasons"]) +
                                   ".  Fares exclude 5% GST." +
                                   ("   FULL - you can join the waitlist." if info["full"] else ""))
        else:
            self.s_dyn.config(text="Select a flight above to compare cabin fares.")

    def run_search(self, silent=False):
        origin, dest = self.s_from.get().strip(), self.s_to.get().strip()
        if not origin or not dest:
            return self.warn("Please select both From and To cities.")
        if origin == dest:
            return self.warn("From and To cannot be the same city.")
        try:
            day = self.s_date.get()
        except ValueError:
            return self.warn("Please select a valid travel date.")
        if day < date.today():
            return self.warn("Travel date cannot be in the past.")
        self.search = {"origin": origin, "dest": dest, "date": day.isoformat()}

        self.s_tree.delete(*self.s_tree.get_children())
        self.row_info = {}
        now = datetime.now()
        results = []
        for f in self.db["flights"]:
            dep = datetime.strptime(f["dep"], DT_FMT)
            if f["origin"] == origin and f["dest"] == dest and dep.date() == day and dep > now:
                results.append((dep, f))
        for _, f in sorted(results, key=lambda x: x[0]):
            taken = len(self.taken_seats(f["id"]))
            factor, reasons = dynamic_factor(f, taken)
            prices = {c: round(f["price"] * m * factor, 2) for c, m in CLASS_MULTIPLIER.items()}
            left = f["seats"] - taken
            d = self.delay_for(f)
            self.row_info[f["id"]] = {"factor": factor, "reasons": reasons, "prices": prices, "full": left <= 0}
            self.s_tree.insert("", "end", iid=f["id"], tags=("full",) if left <= 0 else (), values=(
                f["no"], f["dep"], f["arr"], duration_text(f["dep"], f["arr"]),
                f"{prices['Economy']:,.0f}", f"{prices['Premium Economy']:,.0f}",
                f"{prices['Business']:,.0f}", "FULL - waitlist" if left <= 0 else left,
                f"{d['label']} ({d['prob']:.0%})"))
        n = len(results)
        if n:
            self.s_status.config(
                text=f"{n} flight(s) found: {origin} \u2192 {dest} on {day:%d %b %Y}.  "
                     f"Select a flight, choose a cabin below and press Continue.")
        else:
            self.s_status.config(text="No flights found for this route and date.")
            if not silent:
                messagebox.showinfo("SkyFly", "No flights found for this route and date.\n"
                                              "Try a different date or route.", parent=self)
        self.update_fare_cards()
        return True

    def collect_search(self):
        if not self.search or not self.s_tree.get_children():
            return self.warn("Search for flights first, then select one.")
        sel = self.s_tree.selection()
        if not sel:
            return self.warn("Please select a flight from the results.")
        f = self.find_flight(sel[0])
        full = self.seats_left(f) <= 0
        if full and not messagebox.askyesno(
                "Flight full",
                "This flight is fully booked.\n\nJoin the waitlist? If a confirmed passenger cancels, "
                "the first waitlisted passenger is confirmed automatically and a seat is assigned.",
                parent=self):
            return False
        if not self.flight or self.flight["id"] != f["id"]:
            self.seat = None
            self.recommended = None
        self.flight = f
        self.waitlist = full
        self.cls = self.cls_var.get()
        info = self.row_info[f["id"]]
        self.dyn_factor, self.dyn_reasons = info["factor"], info["reasons"]
        return True

    # ======================================================== STEP 3: MEALS
    def build_meals(self):
        f = self.flight
        self.heading("Meals & Beverages (Optional)",
                     f"Flight {f['no']}  {f['origin']} \u2192 {f['dest']}.  Choose a meal preference and any food "
                     f"you want (up to {MAX_QTY} of each), or skip if you don't want any food.")
        pref_box = ttk.LabelFrame(self.body, text="Meal preference", padding=(12, 6))
        pref_box.pack(fill="x", pady=4)
        ttk.Label(pref_box, text="Special meal").pack(side="left")
        self.pref_combo = ttk.Combobox(pref_box, values=list(PREF_RULES), state="readonly", width=22)
        self.pref_combo.set(self.meal_pref)
        self.pref_combo.pack(side="left", padx=8)
        self.pref_combo.bind("<<ComboboxSelected>>", lambda e: self.apply_meal_pref())
        ttk.Label(pref_box, style="Muted.TLabel",
                  text="Special meals are complimentary. Menu items that do not match are disabled."
                  ).pack(side="left", padx=8)

        wrap = ttk.Frame(self.body)
        wrap.pack(fill="both", expand=True)
        self.meal_total_label = ttk.Label(wrap, text="", style="Total.TLabel")
        legend = ttk.Frame(wrap)
        legend.pack(anchor="w", padx=6)
        for text, color in (("Veg", "#16A34A"), ("Non-Veg", "#B91C1C")):
            tk.Label(legend, text="\u25a0", fg=color, bg=C["bg"]).pack(side="left")
            ttk.Label(legend, text=text, style="Muted.TLabel").pack(side="left", padx=(2, 12))

        grid = ttk.Frame(wrap)
        grid.pack(fill="x")
        grid.columnconfigure(0, weight=1)
        grid.columnconfigure(1, weight=1)
        categories = []
        for item in MENU:
            if item[1] not in categories:
                categories.append(item[1])
        self.meal_vars = {}
        self.meal_widgets = {}
        for n, cat in enumerate(categories):
            box = ttk.LabelFrame(grid, text=cat, padding=(12, 6))
            box.grid(row=n // 2, column=n % 2, sticky="nsew", padx=6, pady=4)
            box.columnconfigure(1, weight=1)
            for r, item in enumerate(i for i in MENU if i[1] == cat):
                iid, _c, name, price, veg, _tags = item
                tk.Label(box, text="\u25a0", fg="#16A34A" if veg else "#B91C1C",
                         bg=C["bg"]).grid(row=r, column=0, sticky="w")
                lbl = ttk.Label(box, text=name)
                lbl.grid(row=r, column=1, sticky="w", padx=6, pady=3)
                ttk.Label(box, text=f"Rs. {price}", style="Bold.TLabel").grid(row=r, column=2, padx=10)
                var = tk.StringVar(value=str(self.meal_qty.get(iid, 0)))
                spin = ttk.Spinbox(box, from_=0, to=MAX_QTY, width=4, textvariable=var,
                                   state="readonly", command=self.update_meal_total)
                spin.grid(row=r, column=3)
                self.meal_vars[iid] = var
                self.meal_widgets[iid] = (lbl, spin, var)

        bar = ttk.Frame(wrap)
        bar.pack(fill="x", pady=(8, 0), padx=6)
        self.meal_total_label.pack(in_=bar, side="left")
        ttk.Button(bar, text="Skip \u2013 I don't want any food", style="Accent.TButton",
                   command=self.skip_meals).pack(side="right")
        ttk.Button(bar, text="Clear selection", command=self.clear_meals).pack(side="right", padx=8)
        self.apply_meal_pref()

    def apply_meal_pref(self):
        pref = self.pref_combo.get()
        for item in MENU:
            lbl, spin, var = self.meal_widgets[item[0]]
            if meal_allowed(item, pref):
                spin.config(state="readonly")
                lbl.config(foreground=C["text"])
            else:
                var.set("0")
                spin.config(state="disabled")
                lbl.config(foreground=C["taken"])
        self.update_meal_total()

    def update_meal_total(self):
        for iid, var in self.meal_vars.items():
            try:
                q = max(0, min(MAX_QTY, int(var.get())))
            except ValueError:
                q = 0
            if q:
                self.meal_qty[iid] = q
            else:
                self.meal_qty.pop(iid, None)
        total = self.meals_total()
        self.meal_total_label.config(text=f"Meals total: {money(total)}" if total else "No food selected")

    def clear_meals(self):
        for var in self.meal_vars.values():
            var.set("0")
        self.update_meal_total()

    def skip_meals(self):
        self.meal_qty = {}
        self.meal_pref = "No preference"
        self.show_step(3)

    def collect_meals(self):
        self.update_meal_total()
        self.meal_pref = self.pref_combo.get()
        return True

    # ====================================================== STEP 4: BAGGAGE
    def build_baggage(self):
        self.heading("Baggage", f"Your {self.cls} fare includes {BAGGAGE_ALLOWANCE[self.cls]:.0f} kg check-in "
                                f"and {CABIN_LIMIT:.0f} kg cabin baggage. Extra baggage is charged automatically.")
        wrap = ttk.Frame(self.body)
        wrap.pack(fill="both", expand=True)
        box = ttk.LabelFrame(wrap, text="Your baggage", padding=14)
        box.pack(side="left", anchor="n", padx=(0, 24))
        self.bag_bags = tk.StringVar(value=str(self.bag["bags"]))
        ttk.Label(box, text="Check-in bags").grid(row=0, column=0, sticky="w", pady=6)
        ttk.Spinbox(box, from_=0, to=4, width=6, textvariable=self.bag_bags, state="readonly",
                    command=self.update_bag_calc).grid(row=0, column=1, sticky="w", padx=10)
        ttk.Label(box, text="Total check-in weight (kg)").grid(row=1, column=0, sticky="w", pady=6)
        self.bag_checkin = ttk.Entry(box, width=10)
        self.bag_checkin.insert(0, f"{self.bag['checkin']:g}")
        self.bag_checkin.grid(row=1, column=1, sticky="w", padx=10)
        ttk.Label(box, text="Cabin bag weight (kg)").grid(row=2, column=0, sticky="w", pady=6)
        self.bag_cabin = ttk.Entry(box, width=10)
        self.bag_cabin.insert(0, f"{self.bag['cabin']:g}")
        self.bag_cabin.grid(row=2, column=1, sticky="w", padx=10)
        ttk.Label(box, text="Special item").grid(row=3, column=0, sticky="w", pady=6)
        self.bag_special = ttk.Combobox(box, values=list(SPECIAL_ITEMS), state="readonly", width=20)
        self.bag_special.set(self.bag["special"])
        self.bag_special.grid(row=3, column=1, sticky="w", padx=10)
        self.bag_special.bind("<<ComboboxSelected>>", lambda e: self.update_bag_calc())
        for e in (self.bag_checkin, self.bag_cabin):
            e.bind("<KeyRelease>", lambda ev: self.update_bag_calc())
        ttk.Label(box, style="Muted.TLabel", justify="left",
                  text=f"Limits: {MAX_CHECKIN_KG:.0f} kg total check-in, {MAX_BAG_KG:.0f} kg per bag,\n"
                       f"{CABIN_MAX:.0f} kg cabin bag.").grid(row=4, column=0, columnspan=2, sticky="w", pady=(10, 0))

        calc = ttk.LabelFrame(wrap, text="Baggage charge (calculated automatically)", padding=14)
        calc.pack(side="left", fill="both", expand=True, anchor="n")
        self.bag_out = tk.Label(calc, text="", justify="left", anchor="nw", bg=C["bg"], fg=C["text"],
                                font=("Courier New", 10))
        self.bag_out.pack(fill="both", expand=True)
        ttk.Label(calc, style="Muted.TLabel", justify="left",
                  text=f"Rates: Rs. {RATE_FIRST_5KG}/kg for the first 5 kg over the allowance, "
                       f"Rs. {RATE_BEYOND}/kg beyond that,\nRs. {RATE_CABIN}/kg for cabin bag over "
                       f"{CABIN_LIMIT:.0f} kg. GST applies.").pack(anchor="w", pady=(10, 0))
        self.update_bag_calc()

    def read_bag_inputs(self):
        try:
            bags = int(self.bag_bags.get())
        except ValueError:
            raise ValueError("Select the number of check-in bags.")
        try:
            checkin = float(self.bag_checkin.get().strip() or 0)
            cabin = float(self.bag_cabin.get().strip() or 0)
        except ValueError:
            raise ValueError("Enter baggage weights as numbers (kg).")
        if checkin < 0 or cabin < 0:
            raise ValueError("Weights cannot be negative.")
        if checkin > MAX_CHECKIN_KG:
            raise ValueError(f"Maximum total check-in weight is {MAX_CHECKIN_KG:.0f} kg.")
        if cabin > CABIN_MAX:
            raise ValueError(f"Maximum cabin bag weight is {CABIN_MAX:.0f} kg.")
        if checkin > 0 and bags == 0:
            raise ValueError("Select at least 1 check-in bag for the declared weight.")
        if bags and checkin / bags > MAX_BAG_KG:
            raise ValueError(f"A single bag cannot exceed {MAX_BAG_KG:.0f} kg. Add another bag.")
        return {"bags": bags, "checkin": checkin, "cabin": cabin, "special": self.bag_special.get()}

    def baggage_lines(self, info, bag):
        lines = [f"Check-in allowance   : {info['allowance']:.1f} kg",
                 f"Declared check-in    : {bag['checkin']:.1f} kg  ({bag['bags']} bag(s))",
                 f"Excess check-in      : {info['excess']:.1f} kg"]
        if info["first"]:
            lines.append(f"  first {info['first']:.1f} kg x Rs.{RATE_FIRST_5KG} = {money(info['first'] * RATE_FIRST_5KG)}")
        if info["rest"]:
            lines.append(f"  next  {info['rest']:.1f} kg x Rs.{RATE_BEYOND} = {money(info['rest'] * RATE_BEYOND)}")
        lines.append(f"Cabin bag            : {bag['cabin']:.1f} kg  (limit {CABIN_LIMIT:.0f} kg)")
        if info["cabin_excess"]:
            lines.append(f"  excess {info['cabin_excess']:.1f} kg x Rs.{RATE_CABIN} = {money(info['cabin_fee'])}")
        lines.append(f"Special item         : {bag['special']}" +
                     (f"  {money(info['special_fee'])}" if info["special_fee"] else ""))
        lines.append("-" * 44)
        lines.append(f"Baggage charge       : {money(info['total'])}" +
                     ("   (within allowance)" if not info["total"] else ""))
        return lines

    def update_bag_calc(self):
        try:
            bag = self.read_bag_inputs()
        except ValueError as e:
            self.bag_out.config(text=str(e), fg="#B91C1C")
            return
        info = baggage_charge(self.cls, bag["checkin"], bag["cabin"], bag["special"])
        self.bag_out.config(text="\n".join(self.baggage_lines(info, bag)), fg=C["text"])

    def collect_baggage(self):
        try:
            self.bag = self.read_bag_inputs()
        except ValueError as e:
            return self.warn(str(e))
        return True

    # ======================================================== STEP 5: SEAT
    def trip_summary(self, parent):
        box = ttk.LabelFrame(parent, text="Trip Summary", padding=12)
        self.summary_box = box
        self.fill_summary()
        return box

    def refresh_summary(self):
        for w in self.summary_box.winfo_children():
            w.destroy()
        self.fill_summary()

    def fill_summary(self):
        box, f, p = self.summary_box, self.flight, self.passenger
        d = self.delay_for(f)
        co2 = co2_estimate(f["origin"], f["dest"], self.cls)
        rows = [
            ("Passenger", f"{p['title']} {p['full_name']}"),
            ("Flight", f"{f['no']}  ({self.cls})"),
            ("Route", f"{f['origin']} \u2192 {f['dest']}"),
            ("Departure", f["dep"]),
            ("Arrival", f["arr"]),
            ("Duration", duration_text(f["dep"], f["arr"])),
            ("Delay outlook", f"{d['label']} ({d['prob']:.0%} chance)"),
        ]
        if co2 is not None:
            rows.append(("CO2 estimate", f"{co2:g} kg per passenger"))
        if self.step >= 4:
            rows.append(("Seat", "Waitlist - assigned later" if self.waitlist else (self.seat or "not selected")))
        for i, (k, v) in enumerate(rows):
            ttk.Label(box, text=k, style="Muted.TLabel").grid(row=i, column=0, sticky="w", pady=1, padx=(0, 12))
            ttk.Label(box, text=v, style="Bold.TLabel").grid(row=i, column=1, sticky="w", pady=1)
        pr = self.pricing()
        lines = [(f"Ticket fare (x{self.dyn_factor:.2f})", money(pr["price"]), "Bold.TLabel"),
                 ("Meals & drinks", money(pr["meals"]) if pr["meals"] else "None", "Bold.TLabel"),
                 ("Baggage", money(pr["bag"]) if pr["bag"] else "Within allowance", "Bold.TLabel")]
        if self.step >= 4 and not self.waitlist:
            lines.append(("Seat fee", money(pr["seat"]) if pr["seat"] else "Free", "Bold.TLabel"))
        lines.append(("GST (5%)", money(pr["gst"]), "Bold.TLabel"))
        if pr["discount"]:
            lines.append(("Loyalty discount", "- " + money(pr["discount"]), "Bold.TLabel"))
        lines.append(("Total payable", money(pr["total"]), "Total.TLabel"))
        r0 = len(rows)
        ttk.Separator(box).grid(row=r0, column=0, columnspan=2, sticky="ew", pady=6)
        for j, (k, v, st) in enumerate(lines):
            ttk.Label(box, text=k, style="Muted.TLabel").grid(row=r0 + 1 + j, column=0, sticky="w", pady=1)
            ttk.Label(box, text=v, style=st).grid(row=r0 + 1 + j, column=1, sticky="w", pady=1)

    def build_seat(self):
        f = self.flight
        if self.waitlist:
            self.heading("Seat Selection", "This flight is full - you are joining the waitlist.")
            wrap = ttk.Frame(self.body)
            wrap.pack(fill="both", expand=True)
            self.trip_summary(wrap).pack(side="left", anchor="n", padx=(0, 24))
            box = ttk.LabelFrame(wrap, text="Waitlist booking", padding=16)
            box.pack(side="left", anchor="n", fill="x", expand=True)
            ttk.Label(box, wraplength=520, justify="left", text=(
                "No seats are available right now, so no seat needs to be chosen.\n\n"
                "\u2022 You pay now; the booking shows as WAITLISTED.\n"
                "\u2022 If a confirmed passenger cancels, the first passenger on the waitlist is confirmed "
                "automatically and given the released seat (free of seat fee).\n"
                "\u2022 If your waitlist booking is cancelled, you get a full refund.\n"
                "\u2022 Use Manage Booking with your PNR to check your status.")).pack(anchor="w")
            self.seat = None
            return
        self.heading("Select Your Seat", "Let Smart Seat Recommendation suggest a seat, or pick one on the map.")
        wrap = ttk.Frame(self.body)
        wrap.pack(fill="both", expand=True)
        self.taken_now = self.taken_seats(f["id"])
        self.exit_ok, self.exit_reason = exit_eligibility(self.passenger)
        self.seat_meta = {lab: seat_info(lab, f) for lab in seat_labels(f["seats"])}
        self.trip_summary(wrap).pack(side="left", anchor="n", padx=(0, 14))

        reco = ttk.LabelFrame(wrap, text="Smart Seat Recommendation", padding=12)
        reco.pack(side="left", anchor="n", padx=(0, 14))
        ttk.Label(reco, text="Seat position").grid(row=0, column=0, sticky="w", pady=3)
        self.rc_pos = ttk.Combobox(reco, values=["No preference", "Window", "Aisle", "Middle"],
                                   state="readonly", width=16)
        self.rc_pos.set("No preference")
        self.rc_pos.grid(row=0, column=1, sticky="w", padx=6)
        ttk.Label(reco, text="Cabin zone").grid(row=1, column=0, sticky="w", pady=3)
        self.rc_zone = ttk.Combobox(reco, values=["No preference", "Front", "Middle", "Back"],
                                    state="readonly", width=16)
        self.rc_zone.set("No preference")
        self.rc_zone.grid(row=1, column=1, sticky="w", padx=6)
        self.rc_legroom = tk.BooleanVar(value=False)
        self.rc_cheap = tk.BooleanVar(value=False)
        self.rc_family = tk.BooleanVar(value=False)
        ttk.Checkbutton(reco, text="Extra legroom", variable=self.rc_legroom).grid(
            row=2, column=0, columnspan=2, sticky="w")
        ttk.Checkbutton(reco, text="Lowest price", variable=self.rc_cheap).grid(
            row=3, column=0, columnspan=2, sticky="w")
        ttk.Checkbutton(reco, text="Travelling with family", variable=self.rc_family,
                        command=self.toggle_family).grid(row=4, column=0, columnspan=2, sticky="w")
        ttk.Label(reco, text="Group size").grid(row=5, column=0, sticky="w", pady=3)
        self.rc_group = tk.StringVar(value="2")
        self.rc_group_spin = ttk.Spinbox(reco, from_=2, to=3, width=4, textvariable=self.rc_group,
                                         state="disabled")
        self.rc_group_spin.grid(row=5, column=1, sticky="w", padx=6)
        ttk.Button(reco, text="Recommend Seat", style="Primary.TButton",
                   command=self.run_recommend).grid(row=6, column=0, columnspan=2, sticky="ew", pady=(10, 6))
        self.rc_result = ttk.Label(reco, text="", style="Total.TLabel", wraplength=250, justify="left")
        self.rc_result.grid(row=7, column=0, columnspan=2, sticky="w")
        self.rc_detail = ttk.Label(reco, text="", style="Muted.TLabel", wraplength=250, justify="left")
        self.rc_detail.grid(row=8, column=0, columnspan=2, sticky="w")
        self.rc_use = ttk.Button(reco, text="Use this seat", command=self.use_recommended, state="disabled")
        self.rc_use.grid(row=9, column=0, columnspan=2, sticky="ew", pady=(8, 0))

        card = ttk.LabelFrame(wrap, text="Seat Map", padding=10)
        card.pack(side="left", fill="both", expand=True)
        legend = ttk.Frame(card)
        legend.pack(pady=(0, 4))
        for text, color in (("Free", C["avail"]), ("Selected", C["ok"]), ("Taken", C["taken"]),
                            ("Suggested", C["reco"]), ("Legroom/Exit", C["legroom"])):
            tk.Label(legend, bg=color, width=2).pack(side="left", padx=(6, 2))
            ttk.Label(legend, text=text, style="Muted.TLabel").pack(side="left")
        ex = sorted(exit_rows(seat_rows(f)))
        if ex and not self.exit_ok:
            ttk.Label(card, foreground="#B91C1C", wraplength=330, justify="left",
                      text=f"Emergency-exit rows {', '.join(map(str, ex))} are restricted for you: "
                           f"{self.exit_reason}.").pack(anchor="w", pady=(0, 4))
        elif ex:
            ttk.Label(card, style="Muted.TLabel", wraplength=330, justify="left",
                      text=f"Rows {', '.join(map(str, ex))} are emergency-exit rows (extra legroom). "
                           f"You are eligible to sit there.").pack(anchor="w", pady=(0, 4))

        grid = ttk.Frame(card)
        grid.pack()
        grid.grid_columnconfigure(3, minsize=26)
        for col, letter in enumerate("ABCDEF"):
            ttk.Label(grid, text=letter, style="Muted.TLabel").grid(row=0, column=col if col < 3 else col + 1)
        self.seat_buttons = {}
        for i, lab in enumerate(seat_labels(f["seats"])):
            r, col = divmod(i, 6)
            btn = tk.Button(grid, text=lab, width=4, relief="flat", bd=0, font=("Segoe UI", 9, "bold"),
                            command=lambda l=lab: self.pick_seat(l))
            m = self.seat_meta[lab]
            if lab in self.taken_now or (m["exit"] and not self.exit_ok):
                btn.config(state="disabled", disabledforeground="white")
            btn.grid(row=r + 1, column=col if col < 3 else col + 1, padx=2, pady=2)
            self.seat_buttons[lab] = btn
        self.seat_info_lbl = ttk.Label(card, text="No seat selected", style="Bold.TLabel")
        self.seat_info_lbl.pack(pady=(8, 0))
        ttk.Label(card, style="Muted.TLabel", justify="center",
                  text="Seat fees: window +Rs.100, aisle +Rs.50, front rows Rs.200, legroom/exit Rs.500"
                  ).pack(pady=(2, 0))
        if self.seat in self.seat_buttons and self.seat not in self.taken_now:
            self.describe_seat()
        else:
            self.seat = None
        self.recommended = None
        self.paint_seats()

    def toggle_family(self):
        self.rc_group_spin.config(state="readonly" if self.rc_family.get() else "disabled")

    def run_recommend(self):
        try:
            group = int(self.rc_group.get()) if self.rc_family.get() else 0
        except ValueError:
            group = 0
        prefs = {"position": self.rc_pos.get(), "zone": self.rc_zone.get(),
                 "legroom": self.rc_legroom.get(), "cheapest": self.rc_cheap.get(), "family": group}
        res = recommend_seat(self.flight, self.taken_now, self.exit_ok, prefs)
        if not res:
            self.rc_result.config(text="No seats available.")
            self.rc_detail.config(text="")
            return
        m = res["meta"]
        self.recommended = res["label"]
        self.rc_result.config(text=f"Recommended Seat: {res['label']}")
        detail = (f"{m['position']} seat, {m['zone']} of the cabin" + (", extra legroom" if m["legroom"] else "") +
                  f". Seat fee: {money(m['fee']) if m['fee'] else 'Free'}.")
        if group >= 2:
            if res["family_ok"]:
                detail += f" Free seats next to it: {', '.join(res['companions'])} (book them separately)."
            else:
                detail += f" No row has {group} free seats together; this is the best single seat."
        self.rc_detail.config(text=detail)
        self.rc_use.state(["!disabled"])
        self.paint_seats()

    def use_recommended(self):
        if self.recommended:
            self.pick_seat(self.recommended)

    def paint_seats(self):
        for lab, btn in self.seat_buttons.items():
            m = self.seat_meta[lab]
            if lab in self.taken_now:
                btn.config(bg=C["taken"], fg="white")
            elif m["exit"] and not self.exit_ok:
                btn.config(bg=C["restricted"], fg="white")
            elif lab == self.seat:
                btn.config(bg=C["ok"], fg="white")
            elif lab == self.recommended:
                btn.config(bg=C["reco"], fg="white")
            elif m["legroom"]:
                btn.config(bg=C["legroom"], fg=C["text"])
            else:
                btn.config(bg=C["avail"], fg=C["text"])

    def describe_seat(self):
        m = self.seat_meta[self.seat]
        self.seat_info_lbl.config(
            text=f"Selected seat: {self.seat}  ({m['position']}, {m['zone']})  "
                 f"seat fee {money(m['fee']) if m['fee'] else 'Free'}")

    def pick_seat(self, label):
        m = self.seat_meta[label]
        if m["exit"] and not messagebox.askyesno(
                "Emergency exit row",
                "You have chosen an emergency-exit seat.\nYou must be willing and able to assist the crew "
                "in an emergency.\n\nContinue with this seat?", parent=self):
            return
        self.seat = label
        self.describe_seat()
        self.paint_seats()
        self.refresh_summary()

    def collect_seat(self):
        if self.waitlist:
            return True
        if not self.seat:
            return self.warn("Please select a seat (or use Smart Seat Recommendation).")
        return True

    # ===================================================== STEP 6: PAYMENT
    def build_payment(self):
        self.heading("Payment", "Review your booking, apply loyalty points and choose a payment method.")
        wrap = ttk.Frame(self.body)
        wrap.pack(fill="both", expand=True)
        self.trip_summary(wrap).pack(side="left", anchor="n", padx=(0, 20))
        right = ttk.Frame(wrap)
        right.pack(side="left", anchor="n", fill="x", expand=True)

        key = self.passenger["phone"]
        bal = self.loyalty_balance(key)
        pr = self.pricing()
        self.max_redeem = min(bal, int(pr["gross"] * MAX_REDEEM_PCT))
        self.points_used = min(self.points_used, self.max_redeem)

        loy = ttk.LabelFrame(right, text="Loyalty Points", padding=12)
        loy.pack(fill="x", pady=(0, 8))
        ttk.Label(loy, text=f"Account: mobile {key[:2]}******{key[-2:]}     Points available: {bal}",
                  style="Bold.TLabel").grid(row=0, column=0, columnspan=4, sticky="w")
        ttk.Label(loy, style="Muted.TLabel",
                  text=f"1 point = Re. 1. You can redeem up to {self.max_redeem} points on this booking "
                       f"(max {int(MAX_REDEEM_PCT * 100)}% of the bill)."
                  ).grid(row=1, column=0, columnspan=4, sticky="w", pady=(2, 6))
        ttk.Label(loy, text="Points to redeem").grid(row=2, column=0, sticky="w")
        self.pts_entry = ttk.Entry(loy, width=10)
        self.pts_entry.insert(0, str(self.points_used))
        self.pts_entry.grid(row=2, column=1, padx=8)
        ttk.Button(loy, text="Apply", command=self.apply_points).grid(row=2, column=2, padx=4)
        ttk.Button(loy, text="Use maximum", command=lambda: self.apply_points(use_max=True)).grid(row=2, column=3)
        self.pts_msg = ttk.Label(loy, text="", style="Muted.TLabel")
        self.pts_msg.grid(row=3, column=0, columnspan=4, sticky="w", pady=(6, 0))
        self.update_points_msg()

        box = ttk.LabelFrame(right, text="Payment Method", padding=12)
        box.pack(fill="x")
        ttk.Label(box, text="Pay using").grid(row=0, column=0, sticky="w", pady=6)
        self.pay_combo = ttk.Combobox(box, values=["UPI", "Credit / Debit Card", "Net Banking", "Wallet"],
                                      state="readonly", width=24)
        self.pay_combo.set(self.payment_method)
        self.pay_combo.grid(row=0, column=1, sticky="w", padx=10)
        self.upi_label = ttk.Label(box, text="UPI ID *")
        self.upi_label.grid(row=1, column=0, sticky="w", pady=6)
        self.upi_entry = ttk.Entry(box, width=27)
        self.upi_entry.insert(0, self.upi_id)
        self.upi_entry.grid(row=1, column=1, sticky="w", padx=10)
        self.upi_hint = ttk.Label(box, text="Example: yourname@okhdfcbank", style="Muted.TLabel")
        self.upi_hint.grid(row=2, column=1, sticky="w", padx=10)
        self.pay_combo.bind("<<ComboboxSelected>>", lambda e: self.toggle_upi())
        ttk.Label(box, text="This is a simulated payment. No real transaction is made and no card "
                            "details are collected.", style="Muted.TLabel", wraplength=430,
                  justify="left").grid(row=3, column=0, columnspan=2, sticky="w", pady=(8, 4))
        self.terms_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(box, variable=self.terms_var,
                        text="I confirm the details are correct and accept the fare rules\n"
                             "(cancellation: 90% refund 24h+ before departure, otherwise 50%;\n"
                             "waitlisted bookings are refunded in full).").grid(
            row=4, column=0, columnspan=2, sticky="w", pady=4)
        self.toggle_upi()

    def update_points_msg(self):
        pr = self.pricing()
        earn = int(pr["total"] // POINTS_PER_RS)
        self.pts_msg.config(text=f"Redeeming {self.points_used} points = {money(pr['discount'])} off.  "
                                 f"You will earn {earn} points on this booking.")

    def apply_points(self, use_max=False):
        if use_max:
            v = self.max_redeem
        else:
            raw = self.pts_entry.get().strip() or "0"
            if not raw.isdigit():
                return self.warn("Enter points as a whole number.", self.pts_entry)
            v = int(raw)
            if v > self.max_redeem:
                self.warn(f"You can redeem at most {self.max_redeem} points on this booking.", self.pts_entry)
                v = self.max_redeem
        self.points_used = v
        self.pts_entry.delete(0, "end")
        self.pts_entry.insert(0, str(v))
        self.update_points_msg()
        self.refresh_summary()
        return True

    def toggle_upi(self):
        is_upi = self.pay_combo.get() == "UPI"
        for w in (self.upi_label, self.upi_entry, self.upi_hint):
            if is_upi:
                w.grid()
            else:
                w.grid_remove()
        if is_upi:
            self.upi_entry.focus_set()

    def collect_payment(self):
        if not self.apply_points():
            return False
        method = self.pay_combo.get()
        upi = ""
        if method == "UPI":
            upi = self.upi_entry.get().strip()
            if not valid_upi(upi):
                return self.warn("Enter a valid UPI ID to pay with UPI (for example name@bank).",
                                 self.upi_entry)
        if not self.terms_var.get():
            return self.warn("Please accept the confirmation and fare rules to continue.")
        self.payment_method = method
        self.upi_id = upi
        self.process_payment()
        return False  # navigation continues after the payment dialog

    def process_payment(self):
        total = self.pricing()["total"]
        dlg = tk.Toplevel(self)
        dlg.title("Processing Payment")
        dlg.transient(self)
        dlg.resizable(False, False)
        if self.upi_id:
            msg = (f"Verifying UPI ID {mask_upi(self.upi_id)} and processing\n"
                   f"payment of {money(total)} ...")
        else:
            msg = f"Processing payment of {money(total)} via {self.payment_method} ..."
        ttk.Label(dlg, text=msg, padding=(24, 20, 24, 10), justify="center").pack()
        pb = ttk.Progressbar(dlg, mode="indeterminate", length=340)
        pb.pack(padx=24, pady=(0, 22))
        pb.start(12)
        dlg.protocol("WM_DELETE_WINDOW", lambda: None)
        self.center_window(dlg, over=self)
        dlg.grab_set()
        self.next_btn.state(["disabled"])

        def done():
            dlg.destroy()
            self.next_btn.state(["!disabled"])
            self.finalize_booking()

        self.after(1600, done)

    def finalize_booking(self):
        f = self.flight
        if not self.waitlist and self.seat in self.taken_seats(f["id"]):
            messagebox.showwarning("SkyFly", "That seat was just taken. Please choose another seat.", parent=self)
            self.seat = None
            self.show_step(4)
            return
        pr = self.pricing()
        key = self.passenger["phone"]
        status = "WAITLISTED" if self.waitlist else "CONFIRMED"
        bag = dict(self.bag)
        bag["fee"] = pr["bag"]
        d = self.delay_for(f)
        booking = {
            "pnr": self.new_pnr(), "flight_id": f["id"], "flight_no": f["no"],
            "origin": f["origin"], "dest": f["dest"], "dep": f["dep"], "arr": f["arr"],
            "cls": self.cls, "seat": None if self.waitlist else self.seat,
            "passenger": dict(self.passenger),
            "dyn_factor": self.dyn_factor, "base_fare": pr["price"],
            "meals": self.meals_list(), "meals_total": pr["meals"], "meal_pref": self.meal_pref,
            "bag": bag, "seat_fee": pr["seat"], "gst": pr["gst"],
            "points_redeemed": int(pr["discount"]), "points_discount": pr["discount"],
            "total": pr["total"], "payment_method": self.payment_method, "upi_id": self.upi_id,
            "co2_kg": co2_estimate(f["origin"], f["dest"], self.cls),
            "delay": d, "status": status, "refund": 0.0, "points_earned": 0,
            "loyalty_key": key, "booked_at": datetime.now().strftime(DT_FMT),
        }
        if pr["discount"]:
            self.add_points(key, -int(pr["discount"]), f"Redeemed on booking {booking['pnr']}")
        if status == "CONFIRMED":
            booking["points_earned"] = int(pr["total"] // POINTS_PER_RS)
            if booking["points_earned"]:
                self.add_points(key, booking["points_earned"], f"Earned on booking {booking['pnr']}")
        self.db["bookings"].append(booking)
        save_db(self.db)
        self.last_booking = booking
        self.show_step(6)

    # ================================================== STEP 7: CONFIRMATION
    def ticket_text(self, b):
        p = b["passenger"]
        idno = p["id_number"]
        masked = "X" * max(len(idno) - 4, 0) + idno[-4:]
        line = "=" * 58

        def row(label, value):
            return f"{label:<19}: {value}"

        status = b["status"]
        if status == "WAITLISTED":
            seat_line = f"Waitlisted - position {self.waitlist_position(b)}"
        else:
            seat_line = b.get("seat") or "-"
        meals = b.get("meals", [])
        if meals:
            meal_lines = [f"{m['qty']} x {m['name']}".ljust(44) + f"{money(m['qty'] * m['price']):>14}"
                          for m in meals]
        else:
            meal_lines = ["No meals selected (skipped)"]
        pref = b.get("meal_pref", "No preference")
        d = b.get("delay")
        co2 = b.get("co2_kg")
        bag = b.get("bag")
        out = [
            line, "SKYFLY AIRLINES  -  E-TICKET".center(58), line,
            row("PNR", b["pnr"]),
            row("Status", status),
            row("Booked on", b["booked_at"]),
            "", "FLIGHT", "-" * 58,
            row("Flight", f"{b['flight_no']}   ({b['cls']})"),
            row("From", b["origin"]),
            row("To", b["dest"]),
            row("Departure", b["dep"]),
            row("Arrival", b["arr"]),
            row("Duration", duration_text(b["dep"], b["arr"])),
            row("Seat", seat_line),
        ]
        if d:
            out.append(row("Delay outlook", f"{d['label']} ({d['prob']:.0%} chance of 15+ min delay)"))
        if co2 is not None:
            trees = max(1, math.ceil(co2 / TREE_KG_PER_YEAR))
            out.append(row("CO2 estimate", f"{co2:g} kg  (~{trees} tree-years to absorb)"))
        out += [
            "", "PASSENGER", "-" * 58,
            row("Name", f"{p['title']} {p['full_name']}"),
            row("Date of birth", f"{p['dob']}  (age {p['age']})"),
            row("Gender", p["gender"]),
            row("Nationality", p["nationality"]),
            row("Special assistance", p.get("assist", "None")),
            row("Email", p["email"]),
            row("Mobile", p["phone"]),
            row("Address", f"{p['address']}, {p['city']}"),
            row("ID proof", f"{p['id_type']} - {masked}"),
            "", "MEALS & BEVERAGES", "-" * 58,
        ]
        if pref != "No preference":
            out.append(row("Meal preference", f"{pref} (complimentary special meal)"))
        out += meal_lines
        out += ["", "BAGGAGE", "-" * 58]
        if bag:
            out += [row("Allowance", f"{BAGGAGE_ALLOWANCE[b['cls']]:.0f} kg check-in, {CABIN_LIMIT:.0f} kg cabin"),
                    row("Declared", f"{bag['checkin']:.1f} kg in {bag['bags']} bag(s); cabin {bag['cabin']:.1f} kg"),
                    row("Special item", bag["special"]),
                    row("Baggage charge", money(bag.get("fee", 0.0)))]
        else:
            out.append("Standard allowance")
        out += ["", "PAYMENT", "-" * 58,
                row("Method", b["payment_method"])]
        if b.get("upi_id"):
            out.append(row("UPI ID", mask_upi(b["upi_id"])))
        out.append(row("Ticket fare", f"{money(b['base_fare'])}  (demand x{b.get('dyn_factor', 1.0):.2f})"))
        if b.get("meals_total"):
            out.append(row("Meals & drinks", money(b["meals_total"])))
        if bag and bag.get("fee"):
            out.append(row("Baggage", money(bag["fee"])))
        if b.get("seat_fee"):
            out.append(row("Seat fee", money(b["seat_fee"])))
        out.append(row("GST (5%)", money(b["gst"])))
        if b.get("points_discount"):
            out.append(row("Loyalty discount", f"- {money(b['points_discount'])}  ({b['points_redeemed']} pts)"))
        out.append(row("Total paid", money(b["total"])))
        if status == "CANCELLED":
            out.append(row("Refund", money(b["refund"])))
        out += ["", "LOYALTY", "-" * 58,
                row("Points earned", b.get("points_earned", 0)),
                row("Points redeemed", b.get("points_redeemed", 0))]
        if status == "WAITLISTED":
            out += [line, "WAITLISTED: you will be confirmed automatically if a seat is released.", line]
        else:
            out += [line, "Please carry a valid photo ID. Check-in closes 45 minutes before departure.", line]
        return "\n".join(out)

    def save_ticket(self, b, parent):
        path = filedialog.asksaveasfilename(
            parent=parent, defaultextension=".txt", initialfile=f"SkyFly_ticket_{b['pnr']}.txt",
            filetypes=[("Text file", "*.txt")])
        if path:
            with open(path, "w", encoding="utf-8") as fh:
                fh.write(self.ticket_text(b))
            messagebox.showinfo("SkyFly", "Ticket saved.", parent=parent)

    def build_confirm(self):
        b = self.last_booking
        p = b["passenger"]
        waitlisted = b["status"] == "WAITLISTED"
        color = C["warn"] if waitlisted else C["ok"]
        banner = tk.Frame(self.body, bg=color)
        banner.pack(fill="x")
        tk.Label(banner, text="\u23f3  Added to Waitlist" if waitlisted else "\u2714  Booking Successful!",
                 font=("Segoe UI", 24, "bold"), fg="white", bg=color).pack(pady=(12, 2))
        tk.Label(banner, text=f"Your PNR:  {b['pnr']}", font=("Segoe UI", 16, "bold"),
                 fg="white", bg=color).pack()
        if waitlisted:
            msg = (f"{p['title']} {p['full_name']}, you are #{self.waitlist_position(b)} on the waitlist for "
                   f"{b['flight_no']}. You will be confirmed automatically if a seat is released.")
        else:
            msg = (f"Thank you for choosing SkyFly, {p['title']} {p['full_name']}. Flight {b['flight_no']} from "
                   f"{b['origin']} to {b['dest']} is confirmed.  Seat {b['seat']}.")
        tk.Label(banner, text=msg, font=("Segoe UI", 10), fg="white", bg=color).pack(pady=(2, 4))
        pts = b.get("points_earned", 0)
        bal = self.loyalty_balance(b["loyalty_key"])
        tk.Label(banner, font=("Segoe UI", 10, "bold"), fg="white", bg=color,
                 text=(f"Loyalty: you earned {pts} points.  Balance: {bal} points." if pts else
                       f"Loyalty: points will be added when your booking is confirmed.  Balance: {bal} points.")
                 ).pack(pady=(0, 10))

        frame = ttk.Frame(self.body)
        frame.pack(fill="both", expand=True, pady=8)
        text = tk.Text(frame, font=("Courier New", 10), wrap="none", bg="white",
                       relief="solid", bd=1, padx=10, pady=8)
        text.insert("1.0", self.ticket_text(b))
        text.config(state="disabled")
        sb = ttk.Scrollbar(frame, orient="vertical", command=text.yview)
        text.configure(yscrollcommand=sb.set)
        text.pack(side="left", fill="both", expand=True)
        sb.pack(side="right", fill="y")

        bar = ttk.Frame(self.body)
        bar.pack(pady=(0, 8))
        if not waitlisted:
            ttk.Button(bar, text="View Boarding Pass (QR)", style="Accent.TButton",
                       command=lambda: self.show_boarding_pass(b)).pack(side="left", padx=6)
        ttk.Button(bar, text="Save Ticket", command=lambda: self.save_ticket(b, self)).pack(side="left", padx=6)
        ttk.Button(bar, text="Book Another Flight", style="Primary.TButton",
                   command=self.new_booking).pack(side="left", padx=6)

    def new_booking(self):
        self.reset_state()
        self.show_step(0)

    # ======================================================= BOARDING PASS
    @staticmethod
    def qr_payload(b):
        p = b["passenger"]
        dep = datetime.strptime(b["dep"], DT_FMT)
        cls = {"Economy": "Y", "Premium Economy": "W", "Business": "J"}[b["cls"]]
        name = f"{p['title']} {p['full_name']}".upper()[:26]
        return (f"SKYFLY|{b['pnr']}|{b['flight_no']}|{dep:%Y%m%d%H%M}|"
                f"{b['origin'][:3].upper()}-{b['dest'][:3].upper()}|{b['seat']}|{name}|{cls}")

    @staticmethod
    def pass_layout(b):
        """(label, value, x, y) tuples shared by the on-screen pass and the SVG export."""
        p = b["passenger"]
        dep = datetime.strptime(b["dep"], DT_FMT)
        gate = f"G{sum(map(ord, b['flight_no'])) % 18 + 1}"
        group = {"Business": "1", "Premium Economy": "2", "Economy": "3"}[b["cls"]]
        return [
            ("PASSENGER", f"{p['title']} {p['full_name']}".upper(), 24, 92),
            ("FROM", b["origin"], 24, 152), ("TO", b["dest"], 210, 152), ("FLIGHT", b["flight_no"], 400, 152),
            ("DATE", dep.strftime("%d %b %Y"), 24, 212), ("DEPARTS", dep.strftime("%H:%M"), 170, 212),
            ("BOARDING", (dep - timedelta(minutes=45)).strftime("%H:%M"), 290, 212), ("GATE", gate, 430, 212),
            ("SEAT", b["seat"], 24, 272), ("GROUP", group, 170, 272), ("CLASS", b["cls"], 290, 272),
            ("PNR", b["pnr"], 430, 272),
        ]

    def show_boarding_pass(self, b):
        if b["status"] != "CONFIRMED" or not b.get("seat"):
            messagebox.showinfo("SkyFly", "A boarding pass is available once the booking is confirmed "
                                          "with a seat.", parent=self)
            return
        dlg = tk.Toplevel(self)
        dlg.title(f"Boarding Pass {b['pnr']}")
        dlg.transient(self)
        dlg.resizable(False, False)
        cv = tk.Canvas(dlg, width=840, height=340, bg="white", highlightthickness=0)
        cv.pack(padx=14, pady=14)
        cv.create_rectangle(2, 2, 838, 338, outline=C["border"], width=2)
        cv.create_rectangle(2, 2, 838, 64, fill=C["primary"], outline=C["primary"])
        cv.create_text(24, 33, text="\u2708  SKYFLY", anchor="w", fill="white", font=("Segoe UI", 20, "bold"))
        cv.create_text(230, 33, text="BOARDING PASS", anchor="w", fill="#BFD3F5", font=("Segoe UI", 13, "bold"))
        cv.create_text(816, 33, text=b["cls"].upper(), anchor="e", fill=C["accent"], font=("Segoe UI", 13, "bold"))
        for label, value, x, y in self.pass_layout(b):
            cv.create_text(x, y, text=label, anchor="w", fill=C["muted"], font=("Segoe UI", 8, "bold"))
            cv.create_text(x, y + 20, text=value, anchor="w", fill=C["text"], font=("Segoe UI", 14, "bold"))
        cv.create_line(570, 80, 570, 322, dash=(4, 4), fill=C["border"])
        qr = make_qr(self.qr_payload(b))
        n = len(qr)
        scale = max(2, 200 // (n + 8))
        side = (n + 8) * scale
        ox, oy = 600, 76
        cv.create_rectangle(ox, oy, ox + side, oy + side, fill="white", outline=C["border"])
        for y, rowv in enumerate(qr):
            for x, dark in enumerate(rowv):
                if dark:
                    px, py = ox + (x + 4) * scale, oy + (y + 4) * scale
                    cv.create_rectangle(px, py, px + scale, py + scale, fill="black", outline="black")
        cv.create_text(ox + side // 2, oy + side + 18, text="Scan at the gate", fill=C["muted"],
                       font=("Segoe UI", 9))
        bar = ttk.Frame(dlg)
        bar.pack(pady=(0, 12))
        ttk.Button(bar, text="Save as SVG", command=lambda: self.save_pass_svg(b, dlg)).pack(side="left", padx=6)
        ttk.Button(bar, text="Close", command=dlg.destroy).pack(side="left", padx=6)
        self.center_window(dlg, over=self)

    def pass_svg(self, b):
        qr = make_qr(self.qr_payload(b))
        n = len(qr)
        scale = 6
        side = (n + 8) * scale
        parts = [f'<svg xmlns="http://www.w3.org/2000/svg" width="900" height="360" viewBox="0 0 900 360" '
                 f'font-family="Segoe UI, Arial, sans-serif">',
                 '<rect x="2" y="2" width="896" height="356" fill="white" stroke="#C9D3E6" stroke-width="2"/>',
                 f'<rect x="2" y="2" width="896" height="64" fill="{C["primary"]}"/>',
                 '<text x="24" y="44" font-size="24" font-weight="bold" fill="white">SKYFLY</text>',
                 '<text x="150" y="42" font-size="15" font-weight="bold" fill="#BFD3F5">BOARDING PASS</text>',
                 f'<text x="876" y="42" font-size="15" font-weight="bold" fill="{C["accent"]}" '
                 f'text-anchor="end">{xml_escape(b["cls"].upper())}</text>']
        for label, value, x, y in self.pass_layout(b):
            parts.append(f'<text x="{x}" y="{y + 4}" font-size="10" font-weight="bold" fill="{C["muted"]}">'
                         f'{xml_escape(label)}</text>')
            parts.append(f'<text x="{x}" y="{y + 26}" font-size="18" font-weight="bold" fill="{C["text"]}">'
                         f'{xml_escape(str(value))}</text>')
        ox, oy = 610, 84
        parts.append(f'<rect x="{ox}" y="{oy}" width="{side}" height="{side}" fill="white" stroke="#C9D3E6"/>')
        for y, rowv in enumerate(qr):
            for x, dark in enumerate(rowv):
                if dark:
                    parts.append(f'<rect x="{ox + (x + 4) * scale}" y="{oy + (y + 4) * scale}" '
                                 f'width="{scale}" height="{scale}" fill="black"/>')
        parts.append('</svg>')
        return "\n".join(parts)

    def save_pass_svg(self, b, parent):
        path = filedialog.asksaveasfilename(
            parent=parent, defaultextension=".svg", initialfile=f"SkyFly_boarding_pass_{b['pnr']}.svg",
            filetypes=[("SVG image", "*.svg")])
        if path:
            with open(path, "w", encoding="utf-8") as fh:
                fh.write(self.pass_svg(b))
            messagebox.showinfo("SkyFly", "Boarding pass saved.", parent=parent)

    # ====================================================== CANCELLATION
    def refund_for(self, b):
        """Returns (percentage, refund amount, error message or None)."""
        if b["status"] == "CANCELLED":
            return 0, 0.0, "This booking is already cancelled."
        dep = datetime.strptime(b["dep"], DT_FMT)
        now = datetime.now()
        if dep <= now:
            return 0, 0.0, "This flight has already departed."
        if b["status"] == "WAITLISTED":
            pct = 1.0
        else:
            pct = 0.9 if (dep - now) >= timedelta(hours=24) else 0.5
        return pct, round(b["total"] * pct, 2), None

    def apply_cancellation(self, b, refund):
        """Cancel, adjust loyalty points, and auto-confirm the first waitlisted passenger."""
        was_confirmed = b["status"] == "CONFIRMED"
        freed_seat = b.get("seat")
        b["status"] = "CANCELLED"
        b["refund"] = refund
        key = b.get("loyalty_key") or b["passenger"]["phone"]
        if b.get("points_redeemed"):
            self.add_points(key, b["points_redeemed"], f"Points returned: booking {b['pnr']} cancelled")
        if b.get("points_earned"):
            self.add_points(key, -b["points_earned"], f"Points reversed: booking {b['pnr']} cancelled")
        promoted = self.promote_waitlist(b["flight_id"], freed_seat) if (was_confirmed and freed_seat) else None
        save_db(self.db)
        return promoted

    def promote_waitlist(self, flight_id, seat):
        f = self.find_flight(flight_id)
        if not f:
            return None
        info = seat_info(seat, f)
        for w in self.db["bookings"]:
            if w["flight_id"] != flight_id or w["status"] != "WAITLISTED":
                continue
            if info["exit"] and not exit_eligibility(w["passenger"])[0]:
                continue  # not eligible for an emergency-exit seat: try the next passenger
            w["status"] = "CONFIRMED"
            w["seat"] = seat
            w["promoted_at"] = datetime.now().strftime(DT_FMT)
            earned = int(w["total"] // POINTS_PER_RS)
            w["points_earned"] = earned
            key = w.get("loyalty_key") or w["passenger"]["phone"]
            if earned:
                self.add_points(key, earned, f"Earned on booking {w['pnr']} (confirmed from waitlist)")
            return w
        return None

    # ====================================================== MANAGE BOOKING
    def open_manage(self):
        dlg = tk.Toplevel(self)
        dlg.title("Manage Booking")
        dlg.geometry("700x720")
        dlg.transient(self)
        dlg.configure(bg=C["bg"])
        top = ttk.Frame(dlg, padding=12)
        top.pack(fill="x")
        ttk.Label(top, text="Enter PNR").pack(side="left")
        pnr_var = tk.StringVar()
        entry = ttk.Entry(top, textvariable=pnr_var, width=16)
        entry.pack(side="left", padx=8)
        ttk.Button(top, text="Find Booking", style="Primary.TButton", command=lambda: show()).pack(side="left")

        text = tk.Text(dlg, font=("Courier New", 10), wrap="none", bg="white", relief="solid", bd=1,
                       padx=10, pady=8, height=30)
        text.pack(fill="both", expand=True, padx=12, pady=4)
        text.config(state="disabled")
        bar = ttk.Frame(dlg, padding=10)
        bar.pack()
        current = {"b": None}
        ttk.Button(bar, text="Cancel Booking", command=lambda: cancel()).pack(side="left", padx=5)
        ttk.Button(bar, text="Boarding Pass", style="Accent.TButton",
                   command=lambda: current["b"] and self.show_boarding_pass(current["b"])).pack(side="left", padx=5)
        ttk.Button(bar, text="Save Ticket",
                   command=lambda: current["b"] and self.save_ticket(current["b"], dlg)).pack(side="left", padx=5)
        ttk.Button(bar, text="Close", command=dlg.destroy).pack(side="left", padx=5)

        def set_text(s):
            text.config(state="normal")
            text.delete("1.0", "end")
            text.insert("1.0", s)
            text.config(state="disabled")

        def show():
            pnr = pnr_var.get().strip().upper()
            b = next((x for x in self.db["bookings"] if x["pnr"] == pnr), None)
            current["b"] = b
            set_text(self.ticket_text(b) if b else "No booking found for this PNR.")

        def cancel():
            b = current["b"]
            if not b:
                messagebox.showinfo("SkyFly", "Find a booking first.", parent=dlg)
                return
            pct, refund, err = self.refund_for(b)
            if err:
                messagebox.showinfo("SkyFly", err, parent=dlg)
                return
            if not messagebox.askyesno(
                    "Cancel booking",
                    f"Refund will be {money(refund)} ({int(pct * 100)}%).\nCancel booking {b['pnr']}?",
                    parent=dlg):
                return
            promoted = self.apply_cancellation(b, refund)
            show()
            note = "Booking cancelled."
            if promoted:
                note += (f"\n\nWaitlist update: booking {promoted['pnr']} (first on the waitlist) was "
                         f"confirmed automatically with seat {promoted['seat']}.")
            messagebox.showinfo("SkyFly", note, parent=dlg)
            self.refresh_all_safe()

        entry.focus_set()
        dlg.bind("<Return>", lambda e: show())
        self.center_window(dlg, over=self)

    def refresh_all_safe(self):
        """Re-run the flight search so seats left / waitlist status stay current."""
        if self.step == 1 and self.search and hasattr(self, "s_tree"):
            try:
                self.run_search(silent=True)
            except tk.TclError:
                pass

    # ============================================================ LOYALTY
    def open_loyalty(self):
        dlg = tk.Toplevel(self)
        dlg.title("Loyalty Points")
        dlg.geometry("520x460")
        dlg.transient(self)
        dlg.configure(bg=C["bg"])
        top = ttk.Frame(dlg, padding=12)
        top.pack(fill="x")
        ttk.Label(top, text="Mobile number").pack(side="left")
        var = tk.StringVar()
        entry = ttk.Entry(top, textvariable=var, width=16)
        entry.pack(side="left", padx=8)
        ttk.Button(top, text="Check Points", style="Primary.TButton", command=lambda: show()).pack(side="left")
        ttk.Label(dlg, text=f"Earn 1 point per Rs. {POINTS_PER_RS} paid. 1 point = Re. 1 off at payment "
                            f"(up to {int(MAX_REDEEM_PCT * 100)}% of a bill).", style="Muted.TLabel",
                  wraplength=480).pack(padx=12, anchor="w")
        out = tk.Text(dlg, font=("Courier New", 10), bg="white", relief="solid", bd=1, padx=10, pady=8, height=16)
        out.pack(fill="both", expand=True, padx=12, pady=10)
        out.config(state="disabled")

        def show():
            key = var.get().strip()
            if not valid_phone(key):
                s = "Enter the 10-digit mobile number used for booking."
            elif key not in self.db["loyalty"]:
                s = "No loyalty account found for this number yet.\nBook a flight to start earning points."
            else:
                acct = self.db["loyalty"][key]
                lines = [f"Mobile {key[:2]}******{key[-2:]}", f"Points balance : {acct['points']}",
                         f"Worth          : {money(acct['points'])}", "", "Recent activity", "-" * 44]
                for h in reversed(acct["history"][-10:]):
                    lines.append(f"{h['date']}  {h['points']:+d}  {h['note']}")
                s = "\n".join(lines)
            out.config(state="normal")
            out.delete("1.0", "end")
            out.insert("1.0", s)
            out.config(state="disabled")

        entry.focus_set()
        dlg.bind("<Return>", lambda e: show())
        self.center_window(dlg, over=self)


if __name__ == "__main__":
    SkyFlyApp().mainloop()
