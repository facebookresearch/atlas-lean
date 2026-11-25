# Kurtz's law of large numbers for SEIR with vital dynamics

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

Then the scaled chain converges to `(s, e, i, r)` in probability, uniformly on every time interval
`[0, T]`: for every real `T` and every `ε > 0`,

`P(∃ t ∈ [0, T], |S_N/N - s| + |E_N/N - e| + |I_N/N - i| + |R_N/N - r| ≥ ε) → 0`  as `N → ∞`.

No positivity or normalisation of the initial point is needed. The event is not assumed measurable;
`P` is applied as an outer measure. The proof applies Kurtz's law of large numbers for stochastic
mass-action systems to the [stochastic mass-action system](chain-crn.md) of the SEIR reaction
network, through the [path bridge](to-crn.md), the
[identification of the ODEs](has-deriv-at-ode-path.md) and the
[identification of the deviations](deviation-to-path.md).

This is Kurtz's law of large numbers for the stochastic SEIR epidemic with vital dynamics (Kurtz
1970, Thm 3.1; Ethier–Kurtz 1986, ch. 11, Thm 2.1).
