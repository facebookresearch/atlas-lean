# SKAT-O statistics of Gaussian phenotypes with mean X α are χ² mixtures

Let `X` be a real `n × q` covariate matrix and `V` a real `n × n` matrix such that `Xᵀ V⁻¹ X` is
invertible, where `V⁻¹` is the inverse of `V`, or `0` when `V` is singular. Let `G` be a real
`n × m` genotype matrix, `a ∈ ℝᵐ` variant weights, `ρ` any real number, `α ∈ ℝ^q` and `V'` any real
`n × n` matrix. If the phenotype `y` has law `N(X α, V')`, the [SKAT-O statistic](skat-oq.md)
`Q_ρ(y)` has the weighted chi-square law

`Q_ρ ~ ∑ⱼ λⱼ(ρ) χ²₁`,

the law of `∑ⱼ λⱼ(ρ) ξⱼ²` for independent standard normal variables `ξ₁, …, ξₙ`, where
`λ₁(ρ), …, λₙ(ρ)` are the eigenvalues, with multiplicity, of `(P V'^{1/2})ᵀ K_ρ (P V'^{1/2})`,
`K_ρ` is the [SKAT-O kernel](skat-okernel.md) and `P = V⁻¹ - V⁻¹ X (Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹` is the
null projection.

Here `N(X α, V')` is the image of the standard Gaussian law on `ℝⁿ` under `z ↦ X α + V'^{1/2} z`.
When `V'` is positive semidefinite, `V'^{1/2}` is its positive semidefinite square root and
`N(X α, V')` is the Gaussian law with mean `X α` and covariance `V'`. For any other `V'`, `V'^{1/2}`
is taken to be `0`: then `N(X α, V')` is the point mass at `X α`, every weight is `0`, and both laws
are the point mass at `0`. Taking `V' = V` gives the null law. The weights are
[nonnegative for `0 ≤ ρ ≤ 1`](eigenvalues-skat-o-nonneg.md).
