# f3 statistic as shared drift on a tree

Let $M$ be a [drift model](../patterson-s-f-statistics/drift-model.md) with [binary loadings](../patterson-s-f-statistics/has-binary-loadings.md) and drift lengths $\ell$. Then for all populations $O, A, B$,

$$f_3(O; A, B) = \sum_{e \in (L_O \triangle L_A) \cap (L_O \triangle L_B)} \ell_e,$$

where $f_3$ is the [f3 statistic](../patterson-s-f-statistics/f3.md) of the population frequencies, $L_X$ the [lineage](../patterson-s-f-statistics/lineage.md) of $X$ and $\triangle$ the symmetric difference: the drift on the edges shared by the paths $O$–$A$ and $O$–$B$ (on a tree, the path from $O$ to the $A$–$B$ path).
