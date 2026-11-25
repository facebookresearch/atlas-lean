# The burden score is the score of the collapsed genotype

For a real `n × q` covariate matrix `X`, a real `n × n` matrix `V`, a real `n × m` genotype matrix
`G`, variant weights `a ∈ ℝᵐ` and every phenotype `y ∈ ℝⁿ`, the [burden score](burden-score.md) is
the score of the collapsed genotype `C = G a`:

`B(y) = ∑ⱼ aⱼ gⱼᵀ P y = Cᵀ P y`,

where `gⱼ` is the column of `G` for variant `j`, `Cᵢ = ∑ⱼ Gᵢⱼ aⱼ` is the `a`-weighted sum of the
minor-allele counts of individual `i`, and `P = V⁻¹ - V⁻¹ X (Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹` is the null
projection. No condition is needed; the inverse of a singular matrix is taken to be `0`.
