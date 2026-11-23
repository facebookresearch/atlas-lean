# For 0 ≤ ρ ≤ 1 the SKAT-O kernel is positive semidefinite

For a real number `ρ` with `0 ≤ ρ ≤ 1`, finitely many individuals, every real `n × m` genotype
matrix `G` and all variant weights `a ∈ ℝᵐ`, the [SKAT-O kernel](skat-okernel.md)
`K_ρ = G diag(a) R_ρ diag(a) Gᵀ`, with `R_ρ = (1 - ρ) I + ρ 𝟙 𝟙ᵀ`, is positive semidefinite. By
the [decomposition](skat-okernel-eq.md) `K_ρ = (1 - ρ) G diag(a²) Gᵀ + ρ (G a)(G a)ᵀ`, it is a
combination with nonnegative coefficients of two positive semidefinite kernels. For `ρ` outside
`[0, 1]` it need not be positive semidefinite.
