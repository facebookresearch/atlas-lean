# Covariance minimality of OLS

**Covariance minimality of OLS** (CH24.3b). Under fixed design `X` with
`IsUnit (Xᵀ * X)`, the model equation `y ω = X *ᵥ β + ε ω`, and homoscedastic uncorrelated
errors `covMatrix p ε = σ ^ 2 • 1` in finite matrix form, any linear estimator
`β̃ ω = A *ᵥ y ω` with `A * X = 1` has covariance at least that of OLS: the difference of the
covariance matrices is positive semidefinite. No mean condition on `ε` is assumed, so this is
covariance minimality only: without `E[ε] = 0` neither estimator need be unbiased. BLUE is
`calibration_blue`, which adds mean-zero errors and a finite error distribution (`0 ≤ p`). The
comparison itself is algebraic and uses only `∑ ω, p ω = 1`. The covariance-minimality step is
`gaussMarkov_covariance_minimality`, reused; the bridge from its unit-noise form is the exact
scaling by `σ ^ 2`.
