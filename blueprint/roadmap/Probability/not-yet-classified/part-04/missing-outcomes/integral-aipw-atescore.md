# Double robustness of the AIPW score for the average treatment effect

For a covariate
with finitely many values, under strong ignorability of the treatment `T` given `X` for the pair
of potential outcomes (`CondIndepDiscrete` plus overlap `0 < P(T | X = x) < 1`), the ATE score
of the observed outcome has mean `E[Y₁ - Y₀]` when **either** the treatment propensity is correct
(`e(x) = P(T | X = x)`) **or** both arm regressions are correct (`m₀(x) = E[Y₀ | X = x]` and
`m₁(x) = E[Y₁ | X = x]`), on every covariate value of positive probability.
