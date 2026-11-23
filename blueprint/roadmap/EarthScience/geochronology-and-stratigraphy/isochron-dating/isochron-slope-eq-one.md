# Isochron slope eq one

Capstone (synthetic isochron): decay constant `lam = log 2 / 10`
(half-life 10 years), age `t = 10`, two samples with parent/reference
ratios `x₁ = 1` and `x₂ = 2`, common initial ratio `b`, and
daughter/reference ratios `yᵢ = b + xᵢ * (exp (lam * t) - 1)`.
The isochron slope `(y₂ - y₁) / (x₂ - x₁)` is `1`: `isochron_slope_eq`
gives `exp (lam * 10) - 1`, and `exp (log 2) = 2`.
