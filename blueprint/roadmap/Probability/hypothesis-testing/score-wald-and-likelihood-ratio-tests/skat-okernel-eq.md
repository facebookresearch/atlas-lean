# The SKAT-O kernel as an affine combination of SKAT and burden kernels

For a real `n × m` genotype matrix `G`, variant weights `a ∈ ℝᵐ` and every real number `ρ`,

`G diag(a) R_ρ diag(a) Gᵀ = (1 - ρ) G diag(a²) Gᵀ + ρ (G a)(G a)ᵀ`,

where `R_ρ = (1 - ρ) I + ρ 𝟙 𝟙ᵀ` and `a²` is the vector of squared weights: the
[SKAT-O kernel](skat-okernel.md) is `1 - ρ` times the
[SKAT kernel](../../../Biology/statistical-genetics/association-tests/skat-variance-component-test/skat-kernel.md) with weights `wⱼ = aⱼ²` plus `ρ`
times the [burden kernel](burden-kernel.md). For `ρ ∈ [0, 1]` this is a convex combination.
