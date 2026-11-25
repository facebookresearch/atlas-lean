# Variance part of the remaining product moment of two coalescence times

For a [ranked labeled history](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md) `h` of `n` genes, sets `s` and `s'` of sampled genes and a natural number `t`,

`D_h(s, s', t) = ∑_{t ≤ u < n - 1} 1[s apart after u] 1[s' apart after u] / C(n - u, 2)²`,

with the [apartness indicator](apart-ind.md) and the [coalescence rate](rate-after.md)
`C(n - u, 2)`, which is positive on this range; for `t ≥ n - 1` the sum is empty and the value
is `0`. In the [Kingman genealogy](kingman-genealogy-measure.md), given the history the epoch lengths are independent and
exponential, the one with `k` lineages of rate `C(k, 2)`, so its variance given `h` is
`1 / C(k, 2)²`; the sum is then the variance, given `h`, of the total length of the epochs that
follow the first `t` events and during which both `s` and `s'` are apart. It is the diagonal
part of the [conditional product moment](future-prod.md) of the remaining coalescence times.
