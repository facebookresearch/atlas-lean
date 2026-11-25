# SKAT-O p-value at a fixed ρ from the null chi-square mixture

For a real `n × q` covariate matrix `X`, a real `n × n` matrix `V` (the null covariance), a real
`n × m` genotype matrix `G`, variant weights `a ∈ ℝᵐ`, a real number `ρ` and a phenotype `y ∈ ℝⁿ`,
the SKAT-O p-value at `ρ` is

`p_ρ(y) = ν_ρ([Q_ρ(y), ∞))`,

where `Q_ρ` is the [SKAT-O statistic](skat-oq.md) and `ν_ρ = ∑ⱼ λⱼ(ρ) χ²₁` is the law of
`∑ⱼ λⱼ(ρ) ξⱼ²` for independent standard normal variables `ξ₁, …, ξₙ`, with `λ₁(ρ), …, λₙ(ρ)` the
eigenvalues of `(P V^{1/2})ᵀ K_ρ (P V^{1/2})`. Here `K_ρ` is the [SKAT-O kernel](skat-okernel.md),
`P = V⁻¹ - V⁻¹ X (Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹` is the null projection, the inverse of a singular matrix being
taken to be `0`, and `V^{1/2}` is the positive semidefinite square root of `V` when `V` is positive
semidefinite and `0` otherwise, in which case `ν_ρ` is the point mass at `0`. The p-value lies in
`[0, 1]` and does not increase with `Q_ρ(y)`. When `Xᵀ V⁻¹ X` is invertible, `ν_ρ` is the
[law of `Q_ρ` under `y ~ N(X α, V)`](map-skat-oq-multivariate-gaussian.md) for every `α`, where
`N(X α, V)` is the Gaussian law with mean `X α` and covariance `V` when `V` is positive semidefinite
and the point mass at `X α` otherwise. So `p_ρ(y) = ℙ₀(Q_ρ ≥ Q_ρ(y))` with `ℙ₀` that law of the
phenotype; for positive semidefinite `V` this is the exact null p-value of `Q_ρ` (Lee, Wu and Lin
2012, §2).
