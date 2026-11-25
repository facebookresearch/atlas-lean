# Unbiasedness of OLS

Under the Gauss-Markov model hypotheses, stated explicitly: fixed design `X` with `Xᵀ * X`
invertible (error-free `x`, including an intercept column where the design has one), errors
with a finite distribution `p` (`0 ≤ p ω` and `∑ ω, p ω = 1`), the model equation
`y ω = X *ᵥ β + ε ω`, and mean-zero errors `E[ε i] = 0`, where `E[f] = ∑ ω, p ω * f ω`, the OLS
estimators satisfy `E[β̂ j] = β j` for the true coefficient vector `β`, componentwise. The
identity holds for any weights with `∑ ω, p ω = 1`; the hypothesis `0 ≤ p ω` makes `p` a
probability distribution, and so makes the identity unbiasedness: for signed weights `E` is not
the mean under any probability distribution. The integral form of this fact is
[the unbiasedness of ordinary least squares for integrable errors](../../../Probability/linear-models-multivariate/ordinary-least-squares/sampling-properties-of-the-ordinary-least-square/integral-ols-estimator-apply.md).
