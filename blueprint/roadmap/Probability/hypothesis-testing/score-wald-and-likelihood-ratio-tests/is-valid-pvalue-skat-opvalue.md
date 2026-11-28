# Each SKAT-O p-value is valid under the null for invertible Xᵀ V⁻¹ X

Let `X` be a real `n × q` covariate matrix and `V` a real `n × n` matrix such that `Xᵀ V⁻¹ X` is
invertible, where `V⁻¹` is the inverse of `V`, or `0` when `V` is singular. Let `G` be a real
`n × m` genotype matrix, `a ∈ ℝᵐ` variant weights, `ρ` any real number and `α ∈ ℝ^q`. Under the
null model `y ~ N(X α, V)` the [SKAT-O p-value](skat-opvalue.md) `p_ρ` is
[valid](../valid-p-values-and-false-discovery-proportion/is-valid-pvalue.md):

`ℙ₀(p_ρ(y) ≤ t) ≤ t` for every `t ∈ [0, 1]`.

Here `N(X α, V)` is the image of the standard Gaussian law on `ℝⁿ` under `z ↦ X α + V^{1/2} z`:
when `V` is positive semidefinite, `V^{1/2}` is its positive semidefinite square root and
`N(X α, V)` is the Gaussian law with mean `X α` and covariance `V`; for any other `V`, `V^{1/2}` is
taken to be `0` and `N(X α, V)` is the point mass at `X α`. The bound holds for every real `ρ`
because `p_ρ(y)` is the upper tail, at the observed value, of the
[exact law of the SKAT-O statistic `Q_ρ`](map-skat-oq-multivariate-gaussian.md) under this model.
