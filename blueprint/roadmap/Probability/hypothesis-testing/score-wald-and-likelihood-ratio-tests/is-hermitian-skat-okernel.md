# The SKAT-O kernel is symmetric for every ρ

For every real `n × m` genotype matrix `G`, all variant weights `a ∈ ℝᵐ` and every real number `ρ`,
the [SKAT-O kernel](skat-okernel.md) `K_ρ = G diag(a) R_ρ diag(a) Gᵀ`, with
`R_ρ = (1 - ρ) I + ρ 𝟙 𝟙ᵀ`, is symmetric: `K_ρᵀ = K_ρ`.
