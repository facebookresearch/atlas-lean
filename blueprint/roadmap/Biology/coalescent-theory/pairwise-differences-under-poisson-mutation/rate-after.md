# Coalescence rate after $u$ coalescence events

For natural numbers `n` and `u`, the real number `C(n - u, 2)`: the number of pairs among the
`n - u` lineages left after `u` coalescence events of a sample of `n` genes, which is the total
coalescence rate of Kingman's coalescent with that many lineages. The subtraction `n - u` is
truncated at `0`, so the value is `0` for `u ≥ n - 1`, when fewer than two lineages remain. It
is positive for `u < n - 1`, that is, at the steps of a [ranked labeled history](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md).
