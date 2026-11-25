# For an a.s. nonzero score vector the covariances sum to zero

Let `P` be a probability measure on a measurable space `Ω` and let the random scores
`Z_0, …, Z_{m-1}` be measurable and almost surely not all zero. Then the covariances of the
[corrected statistics](gc-stat-rv.md), variances included, sum to zero:

`∑ᵢ ∑ₖ Cov(T_i, T_k) = 0`.

The double sum is the variance of `∑ᵢ T_i`, which is the constant `m` almost surely ([constant
sum](sum-gc-stat.md)).
