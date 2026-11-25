# Temperature trapping on a finite time interval

Finite-horizon trapping: for `G, H, B, Tₐ, C > 0` and `t ≥ 0`, if `T` has derivative
`rate(T(s)) / C` within `[0, t]` at every `s ∈ [0, t]` and `T(s) > 0` there (the rate is a thermal
model only for positive temperatures), with `rate` the [net Arrhenius heating
rate](arrhenius-rate.md), then `T(t)` lies in `[lo, hi]` with `lo = min(T(0), Tₐ)` and
`hi = max(T(0), Tₐ + G / H)`. This applies to any solution on `[0, t]`, including a maximal solution
restricted to a compact subinterval of its domain.
