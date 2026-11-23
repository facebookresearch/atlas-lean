# Multi-time law of a Markov family

Let `κ = (κ_t)_{t ≥ 0}` be a family of Markov kernels on `[0, 1]`, `μ` a finite measure on a
measurable space `Ω`, `(𝒢_u)_{u ≥ 0}` a filtration and `Y` a
[Markov family for `κ`](is-kernel-markov-family.md) with respect to `(𝒢_u)` under `μ`. Let
`t = (t_1, …, t_n)` be times with `t_1 ≤ ⋯ ≤ t_n`, let `s ≥ 0` with `s ≤ t_i` for every `i`, and let
`A ∈ 𝒢_s`. Then the law of `(Y_{t_1}, …, Y_{t_n})` under `μ` restricted to `A` is
`∫ Q_{s, t}(y, ·) ν(dy)`, where `ν` is the law of `Y_s` under `μ` restricted to `A` and `Q` is the
[finite-dimensional kernel](../../../../Probability/markov-chains/markov-processes-from-transition-semigroups/finite-chain-kernel.md)
of `κ`.
