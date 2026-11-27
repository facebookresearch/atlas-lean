# Survival in the large-population limit

Let `ν` be a probability measure on `ℕ` (the offspring law), and for every `k ∈ ℕ` let a
[model](is-early-epidemic.md) under a measure `P_k` with offspring law `ν` and population size `N_k`
be given, together with a set `S₀^k` of initially susceptible individuals of its population. Suppose
that `N_k → ∞` and `(N_k − #S₀^k) / N_k → 0`: all but `o(N_k)` individuals are initially susceptible
(an index case inside the population is one of the others). Then for every `n`,
`P_k(I_n ≠ 0) → 1 − 𝓛_n({0})` as `k → ∞`, where `I_n` is the [number of infectives](epi-size.md) of
generation `n` in model `k`, `P_k` of the event is its outer measure if it is not measurable, and
`𝓛_n` is the
[law of the `n`-th generation size](../../../Probability/branching-processes/galton-watson-process/law.md)
of the Galton–Watson process with offspring law `ν`. The limit is
[at least `1 − q`](law-real-zero-le-extinction-prob.md), which is
[positive when `R₀ > 1`](one-sub-extinction-prob-pos.md).
