# Probability that the next event at a level is a mutation

Let `θ > 0` and let `C k`, `M k` be the clocks of a [coalescent with killing](killing-coalescent.md)
of a sample of `n` genes on a probability space `(Ω, μ)`: at each level `2 ≤ k ≤ n`, independent
exponential clocks of rates `k (k - 1) / 2` and `k θ / 2`. For every level `2 ≤ k ≤ n`, the mutation
clock rings strictly before the coalescence clock with probability
`μ{ω : M k ω < C k ω} = θ / (θ + k - 1)`: with `k` lineages, the next event back in time is a
mutation with that probability.
