# Number of lineages of an epoch that separate both of two pairs

For a [ranked labeled history](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md)
`h` of a sample of `n` genes, two sets `s` and `s'` of sampled genes and a natural number `u`,
the overlap count of `s` and `s'` after `u` events is the number of labels `j < n - u` whose
lineage in the
[partition after the first `u` coalescence events](../ranked-labeled-histories-of-coalescent-trees/blocks-after.md)
of `h` holds exactly one gene of `s` and exactly one gene of `s'`.

For `n ≥ 1` and `u ≤ n - 1` that partition has exactly `n - u` lineages, labelled
`0, …, n - u - 1`. The intended range is `u + 2 ≤ n`: the epoch then has `n - u ≥ 2` lineages,
and for pairs `s` and `s'` the count is the number of branches of that epoch that separate both
pairs. At `u = n - 1`, still for `n ≥ 1`, the only lineage holds every gene, so the count is `1`
if `s` and `s'` are both single genes and `0` otherwise, in particular `0` for two pairs. For
`u ≥ n` (every `u` when `n = 0`, where there are no lineages) the truncated difference `n - u` is
`0`, so the count is `0`.
