# With nonnegative parameters and data, I(t) ≥ I(0) exp(−γ t) for t ≥ 0

Let `(S, E, I, R)` be a [solution of the SEIR system](is-solution.md) with `β, σ, γ, N ≥ 0` and
`S(0), E(0), I(0), R(0) ≥ 0`. Then for every `t ≥ 0`,

`I(t) ≥ I(0) e^{-γ t}`:

infectives are removed no faster than at rate `γ`, because `t ↦ I(t) e^{γ t}` is nondecreasing on
`[0, ∞)`, with derivative `σ E(t) e^{γ t} ≥ 0`.
