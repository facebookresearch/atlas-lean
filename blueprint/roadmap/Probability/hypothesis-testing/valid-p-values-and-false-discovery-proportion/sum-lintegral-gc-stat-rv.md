# For an a.s. nonzero score vector the λ̂-corrected means sum to m

Let `P` be a probability measure on a measurable space `Ω` and let the random scores
`Z_0, …, Z_{m-1}` be measurable and almost surely not all zero (`∑ₖ Z_k² ≠ 0` almost surely). Then
the means of the [corrected statistics](gc-stat-rv.md) sum to the number of genes:

`∑ⱼ E[T_j] = m`,

where `E[T_j] = ∫ T_j dP` is the integral of the nonnegative statistic `T_j`. This is the mean of
the identity `∑ⱼ T_j = m` ([constant sum](sum-gc-stat.md)), which holds almost surely.
