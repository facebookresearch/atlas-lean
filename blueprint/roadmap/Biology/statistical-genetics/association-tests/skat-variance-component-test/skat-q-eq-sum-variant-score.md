# SKAT as a weighted sum of squared single-variant scores

For every real `n × q` covariate matrix `X`, real `n × n` matrix `V`, real `n × m` genotype matrix
`G`, real weights `w` and phenotype `y ∈ ℝⁿ`, the [SKAT statistic](skat-q.md) is

`Q = ∑ⱼ wⱼ Sⱼ²`,

with `Sⱼ = gⱼᵀ P y` the [single-variant scores](variant-score.md).
