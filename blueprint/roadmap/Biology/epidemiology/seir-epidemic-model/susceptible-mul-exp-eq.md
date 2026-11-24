# For γ ≠ 0, S(t) exp(β R(t) / (γ N)) is constant for t ≥ 0

Let `(S, E, I, R)` be a [solution of the SEIR system](is-solution.md) with `γ ≠ 0` (`β`, `σ` and
`N` arbitrary), and write `R₀ = β / γ`. Then for every `t ≥ 0`,

`S(t) e^{R₀ R(t) / N} = S(0) e^{R₀ R(0) / N}`,

where the quotients by `N` are read as `0` when `N = 0`, the identity then saying `S(t) = S(0)`.
As for the SIR model, this holds because the latent class enters neither `S'` nor `R'`.
