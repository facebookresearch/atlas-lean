# A variant with no carriers has score zero

If the genotype column of variant `j` is zero, `Gᵢⱼ = 0` for every individual `i`, then for every
real `n × q` covariate matrix `X`, real `n × n` matrix `V` and phenotype `y ∈ ℝⁿ`, its
[single-variant score](variant-score.md) is `Sⱼ = gⱼᵀ P y = 0`.
