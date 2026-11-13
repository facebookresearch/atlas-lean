# Linear moment model for instrumental variables

An observational linear moment model: variables `Z`, `X`, `Y` and `U` on a probability
space, all square integrable, with the algebraic decomposition `Y = α + β X + U`.
The residual `U` is an arbitrary observed-variable function. Consequently `outcome_eq` does not
exclude direct effects of `Z` under interventions, and `β` is only the coefficient in this
decomposition. Orthogonality (`Cov(Z, U) = 0`) and nonzero first stage (`Cov(Z, X) ≠ 0`) are
hypotheses of the covariance identities that use them.
