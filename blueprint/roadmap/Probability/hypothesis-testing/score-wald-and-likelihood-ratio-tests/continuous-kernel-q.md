# The kernel score statistic is continuous in the phenotype

For every real `n × q` covariate matrix `X` and real `n × n` matrices `V` and `K`, the
[kernel score statistic](kernel-q.md) `y ↦ Q_K(y) = (P y)ᵀ K (P y)` is a continuous function on
`ℝⁿ`: it is a quadratic form in `y`. Here `P = V⁻¹ - V⁻¹ X (Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹` is the null
projection, the inverse of a singular matrix being taken to be `0`.
