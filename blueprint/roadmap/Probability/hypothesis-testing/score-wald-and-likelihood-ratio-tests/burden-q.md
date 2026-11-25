# Burden test statistic: the squared burden score

For a real `n × q` covariate matrix `X`, a real `n × n` matrix `V`, a real `n × m` genotype matrix
`G`, variant weights `a ∈ ℝᵐ` and a phenotype `y ∈ ℝⁿ`, the burden test statistic is the square of
the [burden score](burden-score.md),

`Q_B(y) = B(y)² = (∑ⱼ aⱼ Sⱼ(y))²`

(Lee, Wu and Lin 2012, §2), where `Sⱼ(y) = gⱼᵀ P y` are the single-variant scores, `gⱼ` the column
of `G` for variant `j`, and `P = V⁻¹ - V⁻¹ X (Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹` is the null projection, the
inverse of a singular matrix being taken to be `0`. As a square, `Q_B(y) ≥ 0`.
