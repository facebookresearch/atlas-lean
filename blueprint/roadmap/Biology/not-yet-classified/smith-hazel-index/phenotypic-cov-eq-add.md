# Phenotypic covariance decomposes

**Phenotypic covariance decomposes** (multivariate extension whose diagonal recovers Hazel
1943, equation (8)). Let `μ` be a probability measure on `Ω` and `M` a Smith–Hazel model on `n`
traits under `μ`, where `M.orthogonal` assumes `cov[A_i, E_j; μ] = 0` for all trait pairs `i, j`.
Then `M.phenotypicCov = M.geneticCov + M.residualCov` entry by entry; on the diagonal this gives
the single-trait variance decomposition `σ_{X_i}² = σ_{G_i}² + σ_{E_i}²` of Hazel (1943,
equation (8)).
