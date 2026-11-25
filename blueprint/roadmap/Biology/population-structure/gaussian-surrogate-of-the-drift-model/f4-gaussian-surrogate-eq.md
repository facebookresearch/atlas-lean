# A drift model and its matched Gaussian surrogate agree on f4

Let `M` be a [drift model](../patterson-s-f-statistics/drift-model.md) on any measure `μ` (not
necessarily a probability measure), with finitely many populations and edges, lineage weights `w`
and drift lengths `ℓ`, which are [nonnegative](../patterson-s-f-statistics/len-nonneg.md). For every
root mean `m` and all populations `A, B, C, D`, the
[f4 statistic](../patterson-s-f-statistics/f4.md) of the [coordinate frequencies](coord-freq.md)
under the [Gaussian surrogate](gaussian-surrogate.md) `N(m 1, W diag(ℓ) Wᵀ)` built from the
weights and lengths of `M` equals the f4 statistic of the
[population frequencies](../patterson-s-f-statistics/freq.md) of `M`, whatever the root frequency
and the laws of the increments of `M`.
