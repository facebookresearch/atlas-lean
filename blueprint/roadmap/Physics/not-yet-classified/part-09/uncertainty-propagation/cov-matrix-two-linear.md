# Correlated two-input variance

**Correlated two-input variance**, via `covMatrix` entries so the cross term is
explicit: the variance of `a₁ X₁ + a₂ X₂` is
`a₁² Var X₁ + a₂² Var X₂ + 2 a₁ a₂ Cov(X₁, X₂)`, for every weight. The linear combination
is the single entry of a `1 × 2` measurement matrix, so this is
`FiniteProbability.covMatrix_mulVec`; the `2 a₁ a₂` cross term comes from the symmetry
`covariance_comm`, not from any independence assumption.
