# Covariance minimality of OLS

Under fixed design `X` with `Xᵀ * X` invertible, weights `p` with `∑ ω, p ω = 1`, the model
equation `y ω = X *ᵥ β + ε ω`, and homoscedastic uncorrelated errors `Cov(ε) = σ² I`, where
`Cov` is the covariance matrix under `p`, any linear estimator `β̃ ω = A *ᵥ y ω` with
`A * X = 1` has covariance at least that of OLS: the difference of the covariance matrices is
positive semidefinite. No mean condition on `ε` and no sign condition on `p` are assumed, so
this is covariance minimality only: without `E[ε] = 0` neither estimator need be unbiased.
[Gauss-Markov: OLS is BLUE](calibration-blue.md) adds mean-zero errors and `0 ≤ p ω`.
