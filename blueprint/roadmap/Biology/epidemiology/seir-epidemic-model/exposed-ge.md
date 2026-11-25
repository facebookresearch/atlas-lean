# With nonnegative parameters and data, E(t) ≥ E(0) exp(−σ t) for t ≥ 0

Let `(S, E, I, R)` be a [solution of the SEIR system](is-solution.md) with `β, σ, γ, N ≥ 0` and
`S(0), E(0), I(0), R(0) ≥ 0`. Then for every `t ≥ 0`,

`E(t) ≥ E(0) e^{-σ t}`:

the latent class is depleted no faster than at rate `σ`, because `t ↦ E(t) e^{σ t}` is
nondecreasing on `[0, ∞)`, with derivative `β S(t) I(t) e^{σ t} / N ≥ 0` (read as `0` when
`N = 0`).
