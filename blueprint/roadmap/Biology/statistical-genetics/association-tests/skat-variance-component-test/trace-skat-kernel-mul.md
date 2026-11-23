# The trace of the SKAT kernel times a matrix splits over variants

For a real `n × m` genotype matrix `G` with columns `g₁, …, gₘ`, real weights `w` and every real
`n × n` matrix `N`, the [SKAT kernel](skat-kernel.md) `K = G diag(w) Gᵀ` satisfies

`tr(K N) = ∑ⱼ wⱼ gⱼᵀ N gⱼ`,

where `gⱼᵀ N gⱼ = (Gᵀ N G)ⱼⱼ`.
