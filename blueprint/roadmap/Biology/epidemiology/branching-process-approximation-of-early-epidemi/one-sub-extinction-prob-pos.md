# When R₀ > 1, major outbreaks have positive probability

Let `ν` be a probability measure on `ℕ` (the offspring law) with
[mean](../../../Probability/branching-processes/galton-watson-process/mean.md) `R₀ = ∑_k k ν({k})`,
a value in `[0, ∞]`, and suppose `R₀ > 1`. Then `1 − q > 0`, where `q` is
[extinction probability](../../../Probability/branching-processes/galton-watson-process/extinction-prob.md)
`q` of `ν`. By the [large-population limit](tendsto-measure-real-epi-size-ne-zero.md) and the
[convergence](../../../Probability/branching-processes/galton-watson-process/tendsto-law-real-zero.md) of `1 − 𝓛_n({0})` to `1 − q`, `1 − q` is the
probability of a major outbreak, an epidemic that survives `n` generations in the limit of large
populations for every `n`.
