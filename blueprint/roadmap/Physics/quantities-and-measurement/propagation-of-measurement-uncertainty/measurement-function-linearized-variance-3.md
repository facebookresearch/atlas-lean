# First-order law of propagation, uncorrelated inputs

If `f` has derivative `f'` at `x`,
the inputs have standard uncertainties `u i` (`Var[X i] = u i ^ 2`) and are pairwise
uncorrelated, then the first-order combined variance is `∑ i, (∂f/∂xᵢ (x) * u i) ^ 2`. Only
`u i ^ 2` enters, so the sign convention `0 ≤ u i` is not needed. Pairwise independent inputs
are uncorrelated by `ProbabilityTheory.IndepFun.covariance_eq_zero`.
