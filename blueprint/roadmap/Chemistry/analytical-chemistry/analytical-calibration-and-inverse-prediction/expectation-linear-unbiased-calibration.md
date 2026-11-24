# Unbiasedness of a linear estimator

Any estimator `β̃ ω = A *ᵥ y ω` whose matrix satisfies the unbiasedness condition `A * X = 1` has
`E[β̃ j] = β j`, where `E[f] = ∑ ω, p ω * f ω`, under the model equation `y ω = X *ᵥ β + ε ω`,
mean-zero errors `E[ε i] = 0` and a finite error distribution `p` (`0 ≤ p ω` and
`∑ ω, p ω = 1`); no invertibility of `Xᵀ * X` is needed. As for
[OLS](expectation-ols-estimator-calibration.md), the identity holds for any weights with
`∑ ω, p ω = 1`, and `0 ≤ p ω` is what makes `E` the mean under a probability distribution.
