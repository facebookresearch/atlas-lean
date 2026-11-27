# Coalescence time of two sampled genes

Let `h` be a [ranked labeled history](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md) of `n`
genes, `s` a set of sampled genes and `t_k`, for `k = 2, …, n`, real numbers, the lengths of the
epochs (the epoch `k` being the one with `k` lineages). The coalescence time `τ_s` is the sum of
`t_k` over the epochs `k` during which the genes of `s` are [apart](pair-apart.md), that is,
apart after the first `n - k` coalescence events. The epoch lengths enter as given, also when
negative. For a pair `s` of distinct genes and nonnegative epoch lengths, `τ_s` is the time back
from the sample to the most recent common ancestor of the two genes. In general `τ_s` sums the
epoch lengths until some lineage holds all of `s`; for a set of at most one gene no epoch counts
and `τ_s = 0`.
