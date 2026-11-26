# If R₀ > 1 and scaled initial counts tend to positive S, E, I, the chain nears the endemic state

Let `σ > 0`, `γ ≥ 0`, `μ > 0`, and let the
[basic reproduction number](../global-stability-of-the-seir-model/r0.md) satisfy
`R₀ = β σ / ((μ + σ) (μ + γ)) > 1` (so `β > 0`). As in Kurtz's law of large numbers, let `P` be a
probability measure on a space `Ω`. For each scale `N ∈ ℕ` and each [channel](channel.md) `c`, let
`Y_{N,c}` be a
[Poisson process](../../../Probability/point-processes/poisson-processes/is-poisson-process.md) of
rate `1` under `P`; the processes need not be independent. For each `N` let `S_N, E_N, I_N, R_N` be
count paths depending on `ω ∈ Ω` such that, for `P`-almost every `ω`, they form a
[chain path](is-chain-path.md) at scale `N` driven by the paths `Y_{N,c}(·, ω)`. Let `(s, e, i, r)`
be a
[solution of the SEIR system with vital dynamics](../global-stability-of-the-seir-model/is-solution.md)
at scale `1`, `s' = μ - β s i - μ s`, `e' = β s i - (μ + σ) e`, `i' = σ e - (μ + γ) i`,
`r' = γ i - μ r` on `t ≥ 0`, and suppose that the scaled initial state converges to
`(s(0), e(0), i(0), r(0))` in probability: `P(D_N(0) ≥ δ) → 0` for every `δ > 0`, where `D_N` is the
[deviation](deviation.md) of `(S_N, E_N, I_N, R_N) / N` from `(s, e, i, r)`. Suppose moreover that
`s(0) > 0`, `e(0) > 0` and `i(0) > 0`.

Then for every `ε > 0` there is `t₀` such that at each fixed time `t ≥ t₀`,

`P(|S_N(t)/N - S*| + |E_N(t)/N - E*| + |I_N(t)/N - I*| ≥ ε) → 0`  as `N → ∞`,

where `S* = 1 / R₀`, `E* = μ (1 - S*) / (μ + σ)` and `I* = σ E* / (μ + γ)` are the levels of the
endemic equilibrium at scale `1`. The limit is `N → ∞` at fixed `t`; nothing is claimed uniformly in
`t`. The event is not assumed measurable; `P` is applied as an outer measure. The proof combines
Kurtz's law of large numbers with the
[attractivity of the endemic equilibrium from the open positive orthant](../global-stability-of-the-seir-model/tendsto-endemic.md).
