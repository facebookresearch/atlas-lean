# Optimal indices for uncorrelated traits

**Optimal indices for uncorrelated traits** (Hazel 1943, p. 487). Let `μ` be a probability
measure on `Ω` and `M` a Smith–Hazel model on `n` traits under `μ`, with diagonal phenotypic and
additive genetic covariance matrices (`M.phenotypicCov i j = 0` and `M.geneticCov i j = 0` for
`i ≠ j`), `Var[M.aggregate; μ] > 0` and `M.objectiveCov ≠ 0`. For every nonzero coefficient vector
`b`, `b` maximizes `pearsonRatio μ (M.index d) M.aggregate` over all nonzero `d` if and only if
`b = k • (i ↦ M.economic i * M.heritability i)` for some `k > 0`.
