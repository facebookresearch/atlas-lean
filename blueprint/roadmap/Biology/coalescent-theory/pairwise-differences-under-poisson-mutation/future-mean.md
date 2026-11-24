# Conditional mean of the remaining coalescence time given the history

For a [ranked labeled history](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md) `h` of `n` genes, a set `s` of sampled genes and a natural number `t`,

`M_h(s, t) = ∑_{t ≤ u < n - 1} 1[s apart after u] / C(n - u, 2)`,

with the [apartness indicator](apart-ind.md) and the [coalescence rate](rate-after.md)
`C(n - u, 2)`, which is positive on this range. For `t ≥ n - 1` the sum is empty and
`M_h(s, t) = 0`. In the [Kingman genealogy](kingman-genealogy-measure.md), where the epoch with `k` lineages is exponential with
rate `C(k, 2)` independently of the history and so has mean length `1 / C(k, 2)` also given `h`,
it is the mean, given the history `h`, of the part of the coalescence time of `s` after `t`
events: the total length of the epochs that follow the first `t` events and during which `s` is
still apart.
