# Kurtz's law of large numbers for the stochastic SEIR epidemic with vital dynamics

(Kurtz 1970, Thm 3.1; Ethier–Kurtz 1986, ch. 11, Thm 2.1). For each scale `N` let
`(S N, E N, I N, R N)` be the chain driven by unit-rate Poisson processes `Y N c`, one per
channel, i.e. almost every sample path solves the random time-change equations of `IsChainPath`.
Let `(s, e, i, r)` solve the SEIR system with vital dynamics at scale `1`,
`s' = μ - β s i - μ s`, `e' = β s i - (μ + σ) e`, `i' = σ e - (μ + γ) i`, `r' = γ i - μ r`.
If the scaled initial state converges to `(s 0, e 0, i 0, r 0)` in probability, then the scaled
chain converges to `(s, e, i, r)` in probability, uniformly on every time interval `[0, T]`:

`P(∃ t ∈ [0, T], |S/N - s| + |E/N - e| + |I/N - i| + |R/N - r| ≥ ε) → 0`  as `N → ∞`.

No positivity or normalisation of the initial point is needed. The event is not assumed
measurable; `P` is applied as an outer measure. Derived from the mass-action theorem
`StochasticCRNLLN.tendsto_measure_deviation_massAction` through `IsChainPath.toCRN`,
`hasDerivAt_odePath` and `deviation_toPath`.
