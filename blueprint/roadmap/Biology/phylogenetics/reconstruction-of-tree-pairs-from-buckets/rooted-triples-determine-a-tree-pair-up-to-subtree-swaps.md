# Rooted triples determine a pair of trees up to subtree swaps

**Setting.** Let $T_1, T_2$ be labelled rooted phylogenetic trees on the same leaf set $X$. A *cluster* of $T$ is the set of leaves descended from a vertex; a *rooted triple* $ab|c$ is displayed by $T$ when $T|_{\{a,b,c\}}$ has $a, b$ as a cherry. The $3$-bucket $B_3(\{T_1,T_2\})$ is the multiset union of the rooted triples (three-leaf subtrees) of $T_1$ and of $T_2$.

**Theorem (subtree swap invariance).** If there are vertices $x_1$ of $T_1$ and $x_2$ of $T_2$ whose descendant leaf sets are the same set $A \subseteq X$, then the trees $T_3, T_4$ obtained by exchanging the subtrees rooted at $x_1$ and $x_2$ satisfy $B_3(\{T_3,T_4\}) = B_3(\{T_1,T_2\})$. Consequently, for every $n > 4$ there are pairs of distinct labelled trees on $n$ leaves that are not recoverable from their $3$-bucket.

**Theorem (recovery up to swaps).**
1. The multiset of clusters of $T_1$ and $T_2$ (and hence the multiset of their cherries) is recoverable from $B_3(\{T_1,T_2\})$.
2. If $T_1, T_2$ have a $k$-bucket from which the multiset of their clusters is recoverable, then $\{T_1, T_2\}$ is recoverable up to a finite sequence of subtree swaps. In particular, a pair of labelled binary trees is always recoverable from its $3$-bucket up to a finite sequence of subtree swaps.

## Depends on

- [Reconstruction of a pair of phylogenetic trees from its $(n-1)$-bucket](reconstruction-of-tree-pairs-from-one-leaf-deleted-subtrees.md)

## Expansion

A set $Y$ is a cluster of $T$ iff $T$ displays $ab|c$ for all $a, b \in Y$, $c \notin Y$, and a family of sets is the cluster set of a tree iff its members are pairwise nested or disjoint. For a single tree, Aho et al.'s BUILD graph on $Y$ (edges $ab$ for triples $ab|c$ inside $Y$) is the disjoint union of two cliques, the leaf sets of the two root subtrees of $T|_Y$. For a pair of trees the BUILD graph of the bucket is a union of two such discliques; this union decomposes uniquely, so recursing builds the union of the two cluster Hasse diagrams with multiplicities. The clusters fix each tree's shape except for how subtrees with identical leaf sets are distributed between $T_1$ and $T_2$, which is exactly the freedom a subtree swap exploits.

## Sources

- S. Basire and M. Hendriksen, "Tree Buckets and the Reconstruction of Pairs of Phylogenetic Trees", arXiv:2608.25446 (2026), Theorems 5.1, 5.5, 5.6, 5.8, 5.9, 5.10, 5.14 and Corollaries 5.2, 5.11, 5.12, <https://doi.org/10.48550/arXiv.2608.25446>.
- A. V. Aho, Y. Sagiv, T. G. Szymanski and J. D. Ullman, "Inferring a tree from lowest common ancestors with an application to the optimization of relational expressions", SIAM Journal on Computing 10 (1981), <https://doi.org/10.1137/0210030>.
