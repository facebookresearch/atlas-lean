# Species tree with nonnegative branch lengths

A [species tree](species-tree.md) has nonnegative branch lengths if every length stored at one of its nodes, including the unused one at the root, is nonnegative: a leaf always qualifies, and a node $(l, r, t)$ qualifies when $l$ and $r$ do and $t \ge 0$. On such trees the [multispecies coalescent](gene-tree-prob.md) is a probability law on gene trees; with a negative length it is only a signed weight.
