# When R₀ > 1, major outbreaks have positive probability

Let `ν` be a probability measure on `ℕ` (the offspring law) with
[mean](../../../Probability/branching-processes/galton-watson-process/mean.md) `R₀ = ∑_k k ν({k})`,
a value in `[0, ∞]`, and suppose `R₀ > 1`. Then `1 − q > 0`, where `q` is the
[extinction probability](../../../Probability/branching-processes/galton-watson-process/extinction-prob.md)
of `ν`. As the population size `N → ∞` with all but `o(N)` individuals initially susceptible, the
probability that the epidemic survives `n` generations tends to `1 − 𝓛_n({0})`
([large-population limit](tendsto-measure-real-epi-size-ne-zero.md)), where `𝓛_n` is the
[law of the `n`-th generation size](../../../Probability/branching-processes/galton-watson-process/law.md)
of the Galton–Watson process with offspring law `ν`, and `1 − 𝓛_n({0})`
[tends to](../../../Probability/branching-processes/galton-watson-process/tendsto-law-real-zero.md)
`1 − q` as `n → ∞`. So `1 − q` is the probability of a major outbreak, an epidemic that survives `n`
generations in the limit of large populations for every `n`.
