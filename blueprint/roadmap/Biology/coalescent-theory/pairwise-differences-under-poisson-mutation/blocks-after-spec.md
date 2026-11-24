# The $n - t$ blocks after $t \le n - 1$ events form a block partition

Let `h` be a [ranked labeled history](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md) of `n`
genes and `t ≤ n - 1` a natural number. The list of
[lineage blocks after the first `t` coalescence events](../ranked-labeled-histories-of-coalescent-trees/blocks-after.md)
of `h` has `n - t` entries, and for some map `pos` it is a
[block partition](is-block-partition.md) of the sample with positions `pos`: every gene lies in
exactly one of the `n - t` blocks. Here `n - 1` is natural subtraction, so for `n = 0` only
`t = 0` is allowed, and the list is then empty.
