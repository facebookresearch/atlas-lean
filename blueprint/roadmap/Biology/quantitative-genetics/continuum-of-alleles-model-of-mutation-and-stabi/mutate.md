# Mutation step of the continuum-of-alleles model

For [model parameters](params.md) with mutation probability `0 < μ < 1` and mutational standard
deviation `γ > 0`, mutation sends a measure `ρ` on `ℝ` to `(1 - μ) ρ + μ (ρ ∗ N(0, γ²))`: an
allele keeps its effect `x` with probability `1 - μ`, and with probability `μ` it moves to
`x + ξ`, with `ξ` drawn from the [mutation law](mutation-law.md) `N(0, γ²)`.
