# Expected overlap of two paths as an average over histories

Let `s` and `s'` be any two sets of genes of a sample of size `n`. In the
[Kingman genealogy](kingman-genealogy-measure.md) of the sample (independent epoch lengths
`t_2, …, t_n`, `t_k` exponential with rate `C(k, 2) = k (k - 1) / 2`, and an independent ranked
labeled history drawn by
[random joining](../ranked-labeled-histories-of-coalescent-trees/random-joining.md)), the
[total length](pair-path-overlap.md) `ℓ(s, s')` of the branches that hold exactly one gene of
`s` and exactly one gene of `s'` (for pairs: the overlap of the two paths) has mean

`E[ℓ(s, s')] = (1 / H_n) ∑_h ∑_{k=2}^{n} N_k(h) / C(k, 2)`.

Here the sum runs over the
[`H_n = ∏_{k=2}^{n} C(k, 2)` ranked labeled histories](../ranked-labeled-histories-of-coalescent-trees/card-ranked-history.md)
`h` of the sample, each of probability `1 / H_n` under random joining, and `N_k(h)` is the
number of lineages of the epoch of `h` with `k` lineages that hold exactly one gene of `s` and
exactly one gene of `s'`. The inner sum is the
[expected overlap given the history](integral-pair-path-overlap-pi-measure.md).
