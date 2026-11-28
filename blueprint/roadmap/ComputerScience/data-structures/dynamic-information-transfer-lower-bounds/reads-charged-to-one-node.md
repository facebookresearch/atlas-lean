# Each cell read is charged to at most one tree node

In the information-transfer tree of any operation sequence, $\sum_v |\mathrm{IT}(v)|$ is at most the total number of cell reads performed during the sequence. Consequently, if every internal node $v$ at depth $d$ satisfies $|\mathrm{IT}(v)| \ge c \cdot |R_v| \cdot \beta_d$, then the total number of probes is at least $c \sum_d \beta_d \sum_{v \text{ at depth } d} |R_v|$; when the tree is a perfect binary tree over $m = 2^h$ operations, this is $c\, m \sum_{d=0}^{h-1} \beta_d / 2$.

## Proof sketch

A read at time $t$ of a cell last written at time $s < t$ contributes to $\mathrm{IT}(v)$ only for $v$ the lowest common ancestor of the leaves $s$ and $t$, since $s$ must lie in the left and $t$ in the right subtree interval of $v$. Each read is therefore charged at most once. Summing the assumed bound over the internal nodes gives the second claim. In a perfect binary tree over $m = 2^h$ leaves the $2^d$ nodes at depth $d < h$ have disjoint right intervals of $m/2^{d+1}$ operations each, which sum to exactly $m/2$. In an unbalanced tree the sum can be smaller: the root of a tree over three leaves whose right subtree is one leaf has $|R_v| = 1 < 3/2$.

## Depends on

- [Information transfer and the information-transfer tree](information-transfer-tree.md)

## Sources

- Mihai Pătraşcu, Erik D. Demaine, "Logarithmic Lower Bounds in the Cell-Probe Model", SIAM Journal on Computing 35(4) (2006), arXiv:cs/0502041.
