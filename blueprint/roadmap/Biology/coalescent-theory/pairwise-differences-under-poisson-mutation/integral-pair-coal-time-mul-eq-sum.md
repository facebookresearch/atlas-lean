# Product moment of two coalescence times as an average over histories

Let `n ≥ 2` and let `s` and `s'` be pairs of genes of a sample of size `n`, possibly equal. In the
[Kingman genealogy](kingman-genealogy-measure.md) of the sample (independent epoch lengths
`t_2, …, t_n`, `t_k` exponential with rate `C(k, 2) = k (k - 1) / 2`, and an independent ranked
labeled history drawn by
[random joining](../ranked-labeled-histories-of-coalescent-trees/random-joining.md)), the
[coalescence times](pair-coal-time.md) `τ_s` and `τ_{s'}` satisfy

`E[τ_s τ_{s'}] = (1 / H_n) ∑_h (M_s(h) M_{s'}(h) + ∑_{k=2}^{n} A_s(h, k) A_{s'}(h, k) / C(k, 2)²)`.

Here the sum runs over the
[`H_n = ∏_{k=2}^{n} C(k, 2)` ranked labeled histories](../ranked-labeled-histories-of-coalescent-trees/card-ranked-history.md)
`h` of the sample, each of probability `1 / H_n` under random joining; `A_s(h, k)` is `1` if the
two genes of `s` are in different lineages during the epoch of `h` with `k` lineages and `0`
otherwise; and `M_s(h) = ∑_{k=2}^{n} A_s(h, k) / C(k, 2)`. The summand is the
[product moment given the history](integral-pair-coal-time-mul-pi-measure.md).
