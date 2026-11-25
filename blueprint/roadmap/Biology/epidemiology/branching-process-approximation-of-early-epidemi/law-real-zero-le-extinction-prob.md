# Extinction by generation n is at most the extinction probability

Let `ν` be a probability measure on `ℕ` (the offspring law). For every `n`, `𝓛_n({0}) ≤ q`, where
`𝓛_n` is the
[law of the `n`-th generation size](../../../Probability/branching-processes/galton-watson-process/law.md)
of the Galton–Watson process with offspring law `ν` and `q` is the
[extinction probability](../../../Probability/branching-processes/galton-watson-process/extinction-prob.md)
of `ν`.

Equivalently, survival to generation `n` is at least the survival probability:
`1 − q ≤ 1 − 𝓛_n({0})`. As the population size `N → ∞` with all but `o(N)` individuals initially
susceptible, the probability that the epidemic survives `n` generations tends to `1 − 𝓛_n({0})`
([large-population limit](tendsto-measure-real-epi-size-ne-zero.md)).
