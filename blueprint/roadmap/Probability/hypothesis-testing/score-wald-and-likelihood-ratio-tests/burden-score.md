# Burden score: the weighted sum of the single-variant scores

For a real `n × q` covariate matrix `X`, a real `n × n` matrix `V`, a real `n × m` genotype matrix
`G` (in the model, the minor-allele counts of `m` variants), variant weights `a ∈ ℝᵐ` and a
phenotype `y ∈ ℝⁿ`, the burden score is

`B(y) = ∑ⱼ aⱼ Sⱼ(y)`,

the `a`-weighted sum of the
[single-variant scores](../../../Biology/statistical-genetics/association-tests/skat-variance-component-test/variant-score.md) `Sⱼ(y) = gⱼᵀ P y`, where
`gⱼ` is the column of `G` for variant `j` and `P = V⁻¹ - V⁻¹ X (Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹` is the
[null projection](../../../Biology/statistical-genetics/association-tests/skat-variance-component-test/proj-p.md). Any real matrices and weights are
allowed; the inverse of a singular matrix is taken to be `0`. The burden score is also
`Cᵀ P y` for the [collapsed genotype](burden-score-eq.md) `C = G a`.
