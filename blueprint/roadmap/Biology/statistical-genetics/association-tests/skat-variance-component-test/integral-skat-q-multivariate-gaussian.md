# Mean of the SKAT statistic for a Gaussian phenotype with mean X α

Let `X` be a real `n × q` covariate matrix and `V` a real `n × n` matrix such that `Xᵀ V⁻¹ X` is
invertible, where the inverse of a singular matrix is taken to be `0`. Let `G` be a real `n × m`
genotype matrix, `w` real weights, `α ∈ ℝ^q` and `V'` a positive semidefinite real `n × n` matrix.
If `y` has the Gaussian law `N(X α, V')` with mean `X α` in the span of the covariates and
covariance `V'`, the [SKAT statistic](skat-q.md) has mean

`𝔼 Q = tr(K P V' Pᵀ)`,

with `P` the [null projection](proj-p.md) built from `V` and `K` the [SKAT kernel](skat-kernel.md).
