# To HMM

The raw `HMM` structure built from the parameter weights `M.π θ`, `M.P θ`, and `M.e θ`. When
`M` is regular (`M.Regular`) and `θ ∈ M.Θ`, these weights are stochastic with stationary initial
law `M.π θ`, and `likelihood (M.toHMM θ) y n` is the stationary observation probability
`p̄_θ(y_0, …, y_n)`.
