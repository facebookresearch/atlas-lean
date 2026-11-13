# Random assignment, treated arm

If the treatment indicator `1_T` is independent of the
treated potential outcome `Y₁` and `P(T) > 0`, then `∫ Y ∂μ[|T] = ∫ Y₁ ∂μ` for the observed
outcome `Y = observed T Y₀ Y₁` (consistency). No integrability is assumed: the identity holds for
Bochner integrals in general, and when `Y₁` is integrable (as in
`diff_integral_observed_cond_eq_ate_of_indepFun`) both sides are genuine means,
`E[Y | T] = E[Y₁]`; for non-integrable `Y₁` both sides are the conventional value `0`.
