# Expected overlap of two paths given the history

Fix a [ranked labeled history](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md)
`h` of a sample of `n` genes and two sets `s` and `s'` of sampled genes, and let the epoch
lengths `t_2, …, t_n` be independent, `t_k` exponential with rate `C(k, 2) = k (k - 1) / 2`
(the [product law](../kingman-s-coalescent-and-watterson-s-estimator/pi-measure.md) of the
Kingman holding times). Let `ℓ(s, s')` be the [total length](pair-path-overlap.md) of the
branches that hold exactly one gene of `s` and exactly one gene of `s'` (for pairs: the overlap
of the two paths), each of the `k` branches of the epoch with `k` lineages having length
`max(t_k, 0)`. Then

`E[ℓ(s, s')] = ∑_{k=2}^{n} N_k / C(k, 2)`,

where `N_k` is the number of lineages of the epoch with `k` lineages (after `n - k` events of
`h`) that hold exactly one gene of `s` and exactly one gene of `s'`. This is the
[expected remaining overlap](future-overlap.md) at the start of the history.
