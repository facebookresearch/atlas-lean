# Risk Unexposed

The risk among the unexposed, `P(Y = 1 | E = 0) = ∑_z P(z) (1 - e(z)) r₀(z) / (1 - Pe)`. It is
meaningful when `Pe < 1`; if `Pe = 1`, Lean's convention `x / 0 = 0` makes the value `0`.
