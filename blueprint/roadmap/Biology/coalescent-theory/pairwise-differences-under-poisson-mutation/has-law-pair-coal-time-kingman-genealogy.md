# Coalescence time of a pair in the Kingman genealogy is Exp(1)

For `n ≥ 2` and every [pair](../segregating-sites-and-pairwise-differences/sample-pairs.md) `s`
of genes of a sample of size `n`, under the [Kingman genealogy law](kingman-genealogy-measure.md)
(independent epoch lengths, `t_k` exponential with rate `C(k, 2)`, and an independent
random-joining history) the [coalescence time](pair-coal-time.md) `τ_s` of the pair, the sum of
the `t_k` (`2 ≤ k ≤ n`) during which its two genes are in different lineages, has the exponential
law with rate `1`, time being measured in units of `2N` generations. While the pair is apart with
`k` lineages, the next event merges it with probability `1 / C(k, 2)` and comes at rate
`C(k, 2)`, so the pair coalesces at rate one. This is the law of the coalescence times assumed in
[Tajima's expected pairwise differences](../segregating-sites-and-pairwise-differences/integral-mean-pair-diff.md).
