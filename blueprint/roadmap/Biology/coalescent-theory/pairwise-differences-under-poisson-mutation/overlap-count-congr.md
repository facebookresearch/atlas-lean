# The overlap count depends only on the lineages of the four genes

Let `h` be a [ranked labeled history](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md)
of a sample of `n` genes and let `u ≤ n - 1`. Let `a, b, c, d, a', b', c', d'` be genes with
`a ≠ b`, `c ≠ d`, `a' ≠ b'` and `c' ≠ d'` such that, after the first `u` events of `h`, `a` is
in the same lineage as `a'`, `b` as `b'`, `c` as `c'` and `d` as `d'`: every
[labelling of the blocks](is-block-partition.md) after `u` events gives `a` and `a'` the same
label, and likewise for the other three couples. Then the [overlap count](overlap-count.md) of
`{a, b}` and `{c, d}` after `u` events equals that of `{a', b'}` and `{c', d'}`.
