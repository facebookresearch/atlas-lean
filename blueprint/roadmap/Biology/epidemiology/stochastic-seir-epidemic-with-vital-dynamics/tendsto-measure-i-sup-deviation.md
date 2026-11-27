# Kurtz's theorem for SEIR with vital dynamics, supremum form

Let `β`, `σ`, `γ`, `μ` be nonnegative and let `P` be a probability measure on a space `Ω`. For each
scale `N ∈ ℕ` and each [channel](channel.md) `c`, let `Y_{N,c}` be a
[Poisson process](../../../Probability/point-processes/poisson-processes/is-poisson-process.md) of
rate `1` under `P`; the processes need not be independent. For each `N` let `S_N, E_N, I_N, R_N` be
count paths depending on `ω ∈ Ω` such that, for `P`-almost every `ω`, they form a
[chain path](is-chain-path.md) at scale `N` driven by the paths `Y_{N,c}(·, ω)`. Let `(s, e, i, r)`
be a
[solution of the SEIR system with vital dynamics](../global-stability-of-the-seir-model/is-solution.md)
at scale `1`, `s' = μ - β s i - μ s`, `e' = β s i - (μ + σ) e`, `i' = σ e - (μ + γ) i`,
`r' = γ i - μ r` on `t ≥ 0`, and suppose that the scaled initial state converges to
`(s(0), e(0), i(0), r(0))` in probability: `P(D_N(0) ≥ δ) → 0` for every `δ > 0`, where `D_N` is the
[deviation](deviation.md) of `(S_N, E_N, I_N, R_N) / N` from `(s, e, i, r)`.

Then for every real `T` and every `ε > 0`,

`P(sup_{t ∈ [0, T]} D_N(t) ≥ ε) → 0`  as `N → ∞`.

The supremum is taken in `[0, ∞]`, so it exists for every path and need not be attained; the event
is not assumed measurable, and `P` is applied as an outer measure.
