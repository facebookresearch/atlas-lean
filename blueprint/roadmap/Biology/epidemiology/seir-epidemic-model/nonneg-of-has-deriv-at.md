# For β, σ, γ, N ≥ 0, the compartments stay nonnegative on an interval

Let `T` be a real number, and suppose that `S, E, I, R : ℝ → ℝ` satisfy the four SEIR equations

`S' = -β S I / N`,   `E' = β S I / N - σ E`,   `I' = σ E - γ I`,   `R' = γ I`

with two-sided derivatives at every time `t` with `0 ≤ t ≤ T`. If `β, σ, γ, N ≥ 0` and
`S(0), E(0), I(0), R(0) ≥ 0`, then `S(t), E(t), I(t), R(t) ≥ 0` for every such `t`.

The quotient `β S I / N` is read as `0` when `N = 0`, so `N = 0` is allowed. The hypotheses
`β ≥ 0` and `N ≥ 0` make the infection coefficient `β S / N` nonnegative wherever `S ≥ 0`.
