# Nelson Aalen

The delayed-entry **Nelson–Aalen estimate** `Â(t) = ∑_{j ∈ support, tⱼ ≤ t} dⱼ / Yⱼ`.

Only under `GapFree` is this a cumulative-hazard estimate, accumulated from the first supported
time. If the support has a gap, the totalized sum adds hazards from disconnected stretches and
has no cumulative-hazard interpretation.
