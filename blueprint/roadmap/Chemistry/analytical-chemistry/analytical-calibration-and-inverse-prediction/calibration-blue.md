# Gauss-Markov: OLS is BLUE

Under the Gauss-Markov model hypotheses, stated explicitly: fixed design `X` with `Xᵀ * X`
invertible, errors with a finite distribution `p` (`0 ≤ p ω` and `∑ ω, p ω = 1`), the model
equation `y ω = X *ᵥ β + ε ω`, mean-zero errors `E[ε i] = 0`, where `E[f] = ∑ ω, p ω * f ω`, and
homoscedastic uncorrelated errors `Cov(ε) = σ² I`, where `Cov` is the covariance matrix under
`p`: OLS is unbiased, every linear estimator `β̃ ω = A *ᵥ y ω` with `A * X = 1` is unbiased, and
the covariance of `β̃` exceeds that of OLS by a positive semidefinite matrix. The hypothesis
`0 ≤ p ω` makes `p` a probability distribution, without which "unbiased" and "best" have no
probabilistic meaning. The three conclusions are
[the unbiasedness of OLS](expectation-ols-estimator-calibration.md),
[the unbiasedness of a linear estimator](expectation-linear-unbiased-calibration.md) and
[the covariance minimality of OLS](calibration-covariance-minimality.md).
