# Gauss-Markov: OLS is BLUE

**Gauss-Markov: OLS is BLUE** (CH24.3b). Under the Gauss-Markov model hypotheses, stated
explicitly: fixed design `X` with `IsUnit (Xᵀ * X)`, errors with a finite distribution `p`
(`0 ≤ p ω` and `∑ ω, p ω = 1`), the model equation `y ω = X *ᵥ β + ε ω`, mean-zero errors
`E[ε i] = 0` in the MF06 finite-expectation sense, and homoscedastic uncorrelated errors
`covMatrix p ε = σ ^ 2 • 1`: OLS is unbiased, every linear estimator `β̃ ω = A *ᵥ y ω` with
`A * X = 1` is unbiased, and the covariance of `β̃` exceeds that of OLS by a positive
semidefinite matrix. The hypothesis `0 ≤ p ω` makes `p` a probability distribution, without
which "unbiased" and "best" have no probabilistic meaning; it is threaded to the two
unbiasedness lemmas. This combines `expectation_olsEstimator_calibration`,
`expectation_linearUnbiased_calibration` and `calibration_covariance_minimality`.
