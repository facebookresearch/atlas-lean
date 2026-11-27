# Score of an induced pairwise alignment

For every multiple alignment $A$ and rows $i, j$, the [score](../pairwise-sequence-alignment/alignment-score.md) of the [induced pairwise alignment](induced-pair.md) equals $\sum_{c} \kappa(c_i, c_j)$, the sum over the columns $c$ of $A$ of the pairwise [column score](../pairwise-sequence-alignment/column-score.md).
