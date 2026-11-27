# Product moment of two coalescence times given the history

Fix a [ranked labeled history](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md)
`h` of a sample of `n` genes and two sets `s` and `s'` of sampled genes, and let the epoch
lengths `t_2, …, t_n` be independent, `t_k` exponential with rate `C(k, 2) = k (k - 1) / 2`
(the [product law](../kingman-s-coalescent-and-watterson-s-estimator/pi-measure.md) of the
Kingman holding times). For the epoch with `k` lineages, after `n - k` events of `h`, let
`A_s(k)` be `1` if no lineage holds all the genes of `s` (for a pair: if its two genes are in
different lineages) and `0` otherwise, so that `τ_s = ∑_{k=2}^{n} A_s(k) t_k` is the
[coalescence time](pair-coal-time.md) of `s`. Then, with `M_s = ∑_{k=2}^{n} A_s(k) / C(k, 2)`
the mean of `τ_s`,

`E[τ_s τ_{s'}] = M_s M_{s'} + ∑_{k=2}^{n} A_s(k) A_{s'}(k) / C(k, 2)²`:

the product of the means plus the variances `1 / C(k, 2)²` of the epochs during which both `s`
and `s'` are apart. This is the [remaining product moment](future-prod.md) of `s` and `s'` at
the start of the history.
