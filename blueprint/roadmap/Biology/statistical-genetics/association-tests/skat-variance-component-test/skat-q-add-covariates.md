# Covariate effects drop out of the SKAT statistic

Let `X` be a real `n × q` covariate matrix and `V` a real `n × n` matrix such that `Xᵀ V⁻¹ X` is
invertible, where the inverse of a singular matrix is taken to be `0`. Then for every genotype
matrix `G`, real weights `w`, `α ∈ ℝ^q` and `y ∈ ℝⁿ`, the [SKAT statistic](skat-q.md) satisfies

`Q(X α + y) = Q(y)`.
