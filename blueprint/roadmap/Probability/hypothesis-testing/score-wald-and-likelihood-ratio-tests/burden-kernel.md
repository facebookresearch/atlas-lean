# Burden kernel: the outer product of the collapsed genotype

For a real `n × m` genotype matrix `G` and variant weights `a ∈ ℝᵐ`, the burden kernel is the
`n × n` matrix

`K_B = C Cᵀ = G a aᵀ Gᵀ`, with entries `(K_B)ᵢₖ = Cᵢ Cₖ`,

where `C = G a` is the collapsed genotype, `Cᵢ = ∑ⱼ Gᵢⱼ aⱼ`.
