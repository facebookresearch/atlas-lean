# Mean coalescence time of a pair in the Kingman genealogy is one

For `n ≥ 2` and every [pair](../segregating-sites-and-pairwise-differences/sample-pairs.md) `s`
of genes of a sample of size `n`, the [coalescence time](pair-coal-time.md) `τ_s` of the pair,
the sum of the epoch lengths `t_k` (`2 ≤ k ≤ n`) during which its two genes are in different
lineages, has mean `1` under the [Kingman genealogy law](kingman-genealogy-measure.md), with
independent epoch lengths, `t_k` exponential with rate `C(k, 2)`, and an independent
random-joining history; time is in units of `2N` generations. Averaging over the history and the
epoch lengths,

`E τ_s = ∑_{k=2}^n p_{n,k} / C(k, 2) = 1`,

where `p_{n,k} = (k - 1)(n + 1) / ((n - 1)(k + 1))` is the
[probability that the pair is apart](integral-pair-apart-random-joining.md) during the epoch with
`k` lineages and `1 / C(k, 2)` is the mean of `t_k`; the sum is
[evaluated in closed form](../segregating-sites-and-pairwise-differences/sum-pair-separate-prob-div-choose.md).
