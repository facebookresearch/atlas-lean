# Correct outcome regression, treated arm: the weighted residual has conditional mean zero

Under consistency and mean exchangeability for `Y₁`, if the candidate regression is correct,
`m₁(X) = E[Y₁ | X]` a.s., then `E[1_T (Y - m₁(X)) / e(X) | X] = 0` for every measurable candidate
propensity with `e ≥ ε > 0`; the propensity need not be correct.
