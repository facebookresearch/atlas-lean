# Approximation bound for extinction by generation n

For a [model](is-early-epidemic.md) with population size `N` whose offspring law `ν` is a
probability measure, a set `S₀` of initially susceptible individuals of the population and natural
numbers `n` and `L`,

`P(I_n = 0) ≤ 𝓛_n({0}) + ∑_{m < n} 𝓛_{m+1}((L, ∞)) + (n L (N − #S₀) + C(n L, 2)) / N`,

where `I_n` is the [number of infectives](epi-size.md) of generation `n`, `𝓛_n` is the
[law of the `n`-th generation size](../../../Probability/branching-processes/galton-watson-process/law.md)
of the Galton–Watson process with offspring law `ν`, and `P` of the event `{I_n = 0}`, whose
measurability is not assumed, is its outer measure. The middle term bounds the probability that some
generation `1, …, n` of the branching process exceeds `L`, and the last term the probability that
one of the first `n L` contacts is wasted.
