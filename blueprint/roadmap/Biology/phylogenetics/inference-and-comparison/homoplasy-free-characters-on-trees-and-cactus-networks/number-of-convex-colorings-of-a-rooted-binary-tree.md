# Number of convex colorings of a rooted binary tree

**Setting.** Let $\mathcal T$ be a rooted phylogenetic tree with $n$ leaves. A $k$-state character on the leaves is a partition of the leaf set into $k$ nonempty classes (colors, up to renaming). It is *convex* (homoplasy-free) if the coloring can be extended to some internal vertices so that each color class induces a connected rooted subgraph. Let $p_k(\mathcal T)$ be the number of convex $k$-colorings of the leaves and $p(\mathcal T)=\sum_{k\ge 1}p_k(\mathcal T)$, whose reciprocal is proposed as a *specificity* score of the tree.

**Theorem.** If $\mathcal T$ is a rooted binary tree with $n$ leaves, then

$$ p_k(\mathcal T)=\binom{2n-k-1}{k-1} \quad (1\le k\le n), \qquad p(\mathcal T)=F_{2n-1} , $$

where $F_m$ is the $m$-th Fibonacci number ($F_1=F_2=1$). Both numbers depend only on $n$, not on the topology of $\mathcal T$.

## Expansion

Every convex coloring has a unique *minimal* extension: color the lowest common ancestor of each class and the paths from it to the class's leaves, leaving other vertices uncolored, so $p_k$ counts minimal $k$-colorings. Summing $\binom{2n-k-1}{k-1}$ over $k$ is the standard diagonal-sum identity for Fibonacci numbers, giving $F_{2n-1}$; for example $n=2$ gives $1+1=2=F_3$. For non-binary trees and for networks the count does depend on topology, which is why a generating-function recursion is needed there.

## Sources

- N. Alexeev and M. A. Alekseyev, *Combinatorial scoring of phylogenetic networks*, arXiv:1602.02841 (2016). <https://doi.org/10.48550/arXiv.1602.02841> Theorem 1 (Section 2.1, quoting Steel 1992). Published version: Lecture Notes in Computer Science 9797 (2016), 560-572, <https://doi.org/10.1007/978-3-319-42634-1_45>.
- M. Steel, *The complexity of reconstructing trees from qualitative characters and subtrees*, Journal of Classification 9 (1992), 91–116, Proposition 1.
