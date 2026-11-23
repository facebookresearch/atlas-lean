# Strong consistency of empirical Bayes with pooled counts

Units `i = 0, 1, …` (e.g.
genes or donors) each carry a rate drawn from `Gamma(a, b)` and are observed on the same cells
`ι` with size factors `sⱼ > 0`; `Nᵢ` is unit `i`'s pooled count. Suppose the `Nᵢ` are pairwise
independent and identically distributed, and `N₀` has the law of the pooled count:
`P(N₀ = K) = ∑_{∑ⱼ kⱼ = K} pooledMarginalLik a b s k`. Then almost surely the moment estimates
computed from the pooled counts of the first `n` units at the total exposure `S = ∑ⱼ sⱼ`
converge to `(a, b)`, and for every pooled count `K` the empirical-Bayes posterior mean
converges to the oracle pooled posterior mean `(a + K) / (b + S)`. The moment hypotheses of
`HierarchicalCount.ae_tendsto_mom` are derived from the law via `sum_pooledMarginalLik`.
The Gamma-then-Poisson hierarchy is not constructed as a measure here: only the law of `N₀`
(and the pairwise independence and identical distribution of the `Nᵢ`) is assumed.
