# The overlap count in terms of the lineage labels of the genes

Let `h` be a [ranked labeled history](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md)
of a sample of `n` genes, let `u ≤ n - 1`, and let `pos` be a
[labelling of the blocks](is-block-partition.md) of the partition after the first `u` events
of `h`: each gene `g` lies in the block of label `pos g`, and in no other. For genes `a ≠ b`
and `c ≠ d`, the [overlap count](overlap-count.md) of `{a, b}` and `{c, d}` after `u` events is
the number of labels `j < n - u` such that exactly one of `pos a`, `pos b` equals `j` and
exactly one of `pos c`, `pos d` equals `j`.

That is, a lineage separates a pair exactly when it holds exactly one of its two genes.
