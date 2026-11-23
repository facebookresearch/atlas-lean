# Mixture matrix of the SKAT statistic

For a real `n × q` covariate matrix `X`, a real `n × n` matrix `V` (the null covariance), a real
`n × m` genotype matrix `G`, real weights `w` and a real `n × n` matrix `V'` (the phenotype
covariance), the mixture matrix is

`A = (P V'^{1/2})ᵀ K (P V'^{1/2})`,

where `P` is the [null projection](proj-p.md) built from `X` and `V`, `K` the
[SKAT kernel](skat-kernel.md), and `V'^{1/2}` the positive semidefinite square root of `V'` when
`V'` is positive semidefinite. For any other `V'` the square root is taken to be `0`, so `A = 0`.
When `Xᵀ V⁻¹ X` is invertible, the eigenvalues of `A` are the weights of the
[law of the SKAT statistic](map-skat-q-multivariate-gaussian.md) under `y ~ N(X α, V')`; under the
null hypothesis `V' = V`.
