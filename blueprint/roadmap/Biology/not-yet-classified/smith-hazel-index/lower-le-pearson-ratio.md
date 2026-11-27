# Lower bound on the correlation

**Lower bound on the correlation** (Hazel 1943). Let `μ` be a probability measure on `Ω` and `M`
a Smith–Hazel model on `n` traits under `μ`, with `Var[M.aggregate; μ] > 0` and
`M.objectiveCov ≠ 0`. For every nonzero coefficient vector `b`,
`-(√(c ⬝ᵥ w) / σ_H) ≤ pearsonRatio μ (M.index b) M.aggregate`, where `c = M.objectiveCov`,
`w = M.regressionWeights` and `σ_H = populationSD μ M.aggregate`.
