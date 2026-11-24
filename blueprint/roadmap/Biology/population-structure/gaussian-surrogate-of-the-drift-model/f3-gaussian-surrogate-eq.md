# A drift model and its matched Gaussian surrogate agree on f3

Let `M` be a [drift model](../patterson-s-f-statistics/drift-model.md) on any measure `μ` (not
necessarily a probability measure), with finitely many populations and edges, lineage weights `w`
and drift lengths `ℓ`, which are [nonnegative](../patterson-s-f-statistics/len-nonneg.md). For every
root mean `m` and all populations `C, A, B`, the [f3 statistic](../patterson-s-f-statistics/f3.md)
`f3(C; A, B)` of the [coordinate frequencies](coord-freq.md) under the
[Gaussian surrogate](gaussian-surrogate.md) `N(m 1, W diag(ℓ) Wᵀ)` built from the weights and
lengths of `M` equals the f3 statistic of the
[population frequencies](../patterson-s-f-statistics/freq.md) of `M`.
