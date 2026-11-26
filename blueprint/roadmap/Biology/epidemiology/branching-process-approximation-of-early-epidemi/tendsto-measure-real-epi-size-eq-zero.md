# Large-population limit of extinction by generation n

Let `ν` be a probability measure on `ℕ` (the offspring law), and for every `k ∈ ℕ` let a
[model](is-early-epidemic.md) under a measure `P_k` with offspring law `ν` and population size `N_k`
be given, together with a set `S₀^k` of initially susceptible individuals of its population. Suppose
that `N_k → ∞` and `(N_k − #S₀^k) / N_k → 0`: all but `o(N_k)` individuals are initially susceptible
(an index case inside the population is one of the others). Then for every `n`,
`P_k(I_n = 0) → 𝓛_n({0})` as `k → ∞`, where `I_n` is the [number of infectives](epi-size.md) of
generation `n` in model `k`, `P_k` of the event is its outer measure if it is not measurable, and
`𝓛_n` is the
[law of the `n`-th generation size](../../../Probability/branching-processes/galton-watson-process/law.md)
of the Galton–Watson process with offspring law `ν`. As `n → ∞` these values
[increase](../../../Probability/branching-processes/galton-watson-process/monotone-law-real-zero.md)
to
[the extinction probability](../../../Probability/branching-processes/galton-watson-process/tendsto-law-real-zero.md)
`q`, the probability of a minor outbreak.
