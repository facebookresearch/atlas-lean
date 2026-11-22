# Unbiasedness of OLS

**Unbiasedness of OLS** (CH24.3a). Under the Gauss-Markov model hypotheses, stated
explicitly: fixed design `X` with `IsUnit (Xᵀ * X)` (error-free `x`, including an intercept
column where the design has one), errors with a finite distribution `p` (`0 ≤ p ω` and
`∑ ω, p ω = 1`), the model equation `y ω = X *ᵥ β + ε ω`, and mean-zero errors `E[ε i] = 0` in
the MF06 finite-expectation sense, the OLS estimators satisfy `E[β̂ j] = β j` for the true
coefficient vector `β`, componentwise. The proof uses only `∑ ω, p ω = 1`. The hypothesis
`0 ≤ p ω` is still needed for the statement to be unbiasedness: MF06 defines a finite
distribution by both conditions, and for signed weights `expectation p` is not the mean under
any probability distribution. The integral form of this fact is `integral_olsEstimator_apply`;
this finite form is proved here.
