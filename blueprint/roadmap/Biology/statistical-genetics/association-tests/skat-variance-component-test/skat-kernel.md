# Weighted linear SKAT kernel

For a real `n × m` genotype matrix `G` (individuals × variants, entries the minor-allele counts) and
real variant weights `w₁, …, wₘ`, the weighted linear SKAT kernel is the `n × n` matrix

`K = G W Gᵀ`, `W = diag(w)`,

so `Kᵢₗ = ∑ⱼ wⱼ Gᵢⱼ Gₗⱼ`. The weights are arbitrary real numbers; the SKAT weights are nonnegative.
