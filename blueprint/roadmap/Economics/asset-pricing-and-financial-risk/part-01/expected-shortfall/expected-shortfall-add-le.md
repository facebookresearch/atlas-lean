# Subadditivity of expected shortfall

For losses `X` and `Y` on a finite sample space with weights `p(ω) ≥ 0` summing to `1` and a
level `0 < α < 1`, `ES_α(X + Y) ≤ ES_α(X) + ES_α(Y)`, where
`ES_α(Z) = inf_c (c + E[(Z - c)⁺] / (1 - α))` (infimum over real `c`) with
`E[(Z - c)⁺] = ∑_ω p(ω) max(Z(ω) - c, 0)`.
