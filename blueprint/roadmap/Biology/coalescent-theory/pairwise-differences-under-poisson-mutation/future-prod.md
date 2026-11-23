# Conditional product moment of the remaining coalescence times

For a [ranked labeled history](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md) `h` of `n` genes, sets `s` and `s'` of sampled genes and a natural number `t`,

`P_h(s, s', t) = M_h(s, t) M_h(s', t) + D_h(s, s', t)`,

where `M_h` is the [conditional mean of the remaining coalescence time](future-mean.md) and
`D_h` its [variance part](future-diag.md); it is `0` for `t ≥ n - 1`. In the [Kingman genealogy](kingman-genealogy-measure.md),
with independent exponential epochs, the epoch with `k` lineages having rate `C(k, 2)`, it is the
mean, given `h`, of the product of the parts of the coalescence times of `s` and `s'` after `t`
events.
