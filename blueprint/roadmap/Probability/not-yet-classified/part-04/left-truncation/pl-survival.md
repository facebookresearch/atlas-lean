# Pl Survival

The delayed-entry **product-limit estimate** `Ŝ(t) = ∏_{j ∈ support, tⱼ ≤ t} (1 - dⱼ / Yⱼ)`.

Grid times with nobody at risk are excluded: the data identify no hazard there. Only under
`GapFree` is this an estimate of survival, conditional on reaching the first supported time and
normalized there, not at time zero. If the support has a gap, the totalized product multiplies
across disconnected stretches and has no survival interpretation.
