# Temperature trapping for all forward time

Forward trapping for a solution defined for all `t ≥ 0`: for `G, H, B, Tₐ, C > 0`, if `T(s) > 0` and
`T` has derivative `rate(T(s)) / C` within `[0, ∞)` at every `s ≥ 0`, with `rate` the [net Arrhenius
heating rate](arrhenius-rate.md), then for every `t ≥ 0`, `T(t)` lies in `[lo, hi]` with
`lo = min(T(0), Tₐ)` and `hi = max(T(0), Tₐ + G / H)`. It follows from [trapping on each
interval](arrhenius-solution-trapped-on-interval.md) `[0, t]`; it presupposes a solution existing
for all forward time and does not assert global existence.
