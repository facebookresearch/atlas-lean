# Variance of a linear combination of inputs

The variance of a linear combination of input quantities with finite second moments on a
probability space is `Var[∑ i, a i * X i] = ∑ i, ∑ j, a i * a j * cov[X i, X j]`, exactly. This
is a specialization of Mathlib's `ProbabilityTheory.variance_fun_sum`, using
`MemLp.const_mul` and `covariance_const_mul_left` / `covariance_const_mul_right`.
