# Genetic gain

**Genetic gain** (Hazel 1943, equation (3)). Let `μ` be a probability measure on `Ω` and `M` a
Smith–Hazel model on `n` traits under `μ` whose additive values and residuals `(A, E)` are jointly
Gaussian under `μ`, with `Var[M.aggregate; μ] > 0`. For every nonzero coefficient vector `b` and
every threshold `z`,
`M.gain b z = inverseMillsRatio (-z) * pearsonRatio μ (M.index b) M.aggregate * σ_H`, where
`σ_H = populationSD μ M.aggregate`.
