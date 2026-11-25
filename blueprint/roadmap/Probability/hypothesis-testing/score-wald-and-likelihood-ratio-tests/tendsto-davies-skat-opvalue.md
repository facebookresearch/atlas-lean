# Davies' integral gives the SKAT-O p-value when some weight is nonzero

Let `X` be a real `n × q` covariate matrix, `V` a real `n × n` matrix, `G` a real `n × m` genotype
matrix, `a ∈ ℝᵐ` variant weights, `ρ` a real number and `y ∈ ℝⁿ`. Let `λ₁(ρ), …, λₙ(ρ)` be the
eigenvalues of `(P V^{1/2})ᵀ K_ρ (P V^{1/2})`, where `K_ρ` is the [SKAT-O kernel](skat-okernel.md),
`P = V⁻¹ - V⁻¹ X (Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹` is the null projection, the inverse of a singular matrix being
taken to be `0`, and `V^{1/2}` is the positive semidefinite square root of `V` when `V` is positive
semidefinite and `0` otherwise. Let `φ(t) = ∏ⱼ (1 - 2 i λⱼ(ρ) t)^{-1/2}` (principal branch). If some
`λⱼ(ρ)` is nonzero, then, as `T → ∞`, with `c = Q_ρ(y)` the observed [SKAT-O statistic](skat-oq.md),

`1/2 + π⁻¹ ∫₀^T Im(e^{-i t c} φ(t)) / t dt → p_ρ(y)`,

the [SKAT-O p-value](skat-opvalue.md) `p_ρ(y) = ν_ρ([c, ∞))` of the law `ν_ρ = ∑ⱼ λⱼ(ρ) χ²₁`. With a
nonzero weight `ν_ρ` has no atoms, so the tails `ν_ρ((c, ∞))` and `ν_ρ([c, ∞))` agree; with every
weight `0` and `Q_ρ(y) = 0`, the integral tends to `1/2` while `p_ρ(y) = 1`. No condition on `X` is
needed; when `Xᵀ V⁻¹ X` is invertible, `p_ρ(y)` is the null probability `ℙ₀(Q_ρ ≥ Q_ρ(y))` under
`y ~ N(X α, V)` (the Gaussian law with mean `X α` and covariance `V` when `V` is positive
semidefinite, the point mass at `X α` otherwise), and it is
[valid](is-valid-pvalue-skat-opvalue.md).
