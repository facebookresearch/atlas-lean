# Genes that have coalesced share their lineage label from then on

Let `h` be a [ranked labeled history](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md)
of a sample of `n` genes, and let `g` and `g'` be genes in the same lineage after the first `t`
events of `h`. Then for every `u ≥ t` and every [labelling](is-block-partition.md) `pos` of the
blocks of the partition after `u` events (each gene `x` lies in the block of label `pos x`, and
in no other), `pos g = pos g'`.
