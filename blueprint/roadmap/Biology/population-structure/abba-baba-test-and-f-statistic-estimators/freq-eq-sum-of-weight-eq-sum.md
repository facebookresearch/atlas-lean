# Frequencies mix like lineage weights in the drift model

In a [drift model](../patterson-s-f-statistics/drift-model.md) with lineage weights `w`, let `T` be
a population and `S k` source populations indexed by a finite set, with real coefficients `c k` of
any sign and `∑ k, c k = 1`. If the lineage weights of `T` are the affine combination
`w T e = ∑ k, c k * w (S k) e` of those of the sources for every edge `e`, with no extra term for a
private edge of `T`, then at every outcome `ω` the [frequency](../patterson-s-f-statistics/freq.md)
of `T` is the same combination of the source frequencies: `p T ω = ∑ k, c k * p (S k) ω`. For
nonnegative coefficients such a `T` is a mixture of the sources with zero private drift.
