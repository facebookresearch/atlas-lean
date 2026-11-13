# Gumbel Level

The **Gumbel level** `x_α = log (K / (-log (1 - α))) / θ`: the centered threshold at which the
Gumbel distribution function `exp (-K e^{-θ x})` equals `1 - α`. The p-value `gumbelPValue K θ n s`
is at most `α` exactly when `s ≥ log n / θ + x_α`.
