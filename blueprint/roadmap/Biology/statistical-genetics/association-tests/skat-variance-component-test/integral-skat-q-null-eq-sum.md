# The null mean of the SKAT statistic splits over variants

Let `V` be a positive definite real `n × n` matrix and `X` a real `n × q` covariate matrix such that
`Xᵀ V⁻¹ X` is invertible, and let `α ∈ ℝ^q`, `G` a real `n × m` genotype matrix and `w` real
weights. Under the null hypothesis `y ~ N(X α, V)`, the Gaussian law with mean `X α` in the span of
the covariates and covariance `V`, the [SKAT statistic](skat-q.md) has mean

`𝔼₀ Q = ∑ⱼ wⱼ gⱼᵀ P gⱼ`,

where `gⱼ` is the genotype column of variant `j` and `P` the [null projection](proj-p.md). A variant
enters the null mean only through its weight `wⱼ` times the quadratic form of its genotype column.
