# Expected remaining overlap of two paths given the history

For a [ranked labeled history](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md)
`h` of a sample of `n` genes, two sets `s` and `s'` of sampled genes and a natural number `t`,

`F_t(h; s, s') = ∑_{t ≤ u < n - 1} N_u(h; s, s') / C(n - u, 2)`,

where `N_u(h; s, s')` is the [overlap count](overlap-count.md) of `s` and `s'` after `u` events
(the number of lineages after the first `u` events of `h` that hold exactly one gene of `s` and
exactly one gene of `s'`) and `C(m, 2) = m (m - 1) / 2`. Each divisor `C(n - u, 2)` with
`u ≤ n - 2` is at least `1`. For `t ≥ n - 1` the sum is empty and `F_t(h; s, s') = 0`.

In the Kingman genealogy the epoch with `k` lineages has an exponential length of rate `C(k, 2)`,
hence mean `1 / C(k, 2)`, independently of the history. There `F_t(h; s, s')` is the expected
total length, given `h`, of the branches after the first `t` events that hold exactly one gene
of each set (for pairs: that separate both pairs); for `t = 0` this is the
[expected overlap of two paths given the history](integral-pair-path-overlap-pi-measure.md).
