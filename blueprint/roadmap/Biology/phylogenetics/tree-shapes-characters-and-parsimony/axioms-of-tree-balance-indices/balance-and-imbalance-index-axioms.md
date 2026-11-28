# Balance and imbalance index axioms for rooted tree shapes

**Setting.** A *tree* is a rooted tree with no vertex of out-degree $1$; write $\mathcal{T}^\ast_n$ for the set of (isomorphism classes of) rooted trees with $n$ leaves and $\mathcal{BT}^\ast_n\subseteq\mathcal{T}^\ast_n$ for the rooted binary trees. The *caterpillar* $T^{cat}_n$ is the binary tree with $n$ leaves and exactly one cherry (or the single vertex if $n=1$); the *fully balanced tree* $T^{fb}_h$ is the binary tree with $n=2^h$ leaves all at depth $h$. A *(rooted binary) tree shape statistic* is a map $t:\mathcal{T}^\ast\to\mathbb{R}_{\ge 0}$ (respectively $t:\mathcal{BT}^\ast\to\mathbb{R}_{\ge0}$) that depends only on the tree shape, not on leaf labels or edge lengths.

**Definition (balance index).** A tree shape statistic $t$ is a *balance index* if and only if

1. the caterpillar $T^{cat}_n$ is the unique tree minimizing $t$ on $\mathcal{T}^\ast_n$ (respectively $\mathcal{BT}^\ast_n$) for every $n\ge1$, and
2. the fully balanced tree $T^{fb}_h$ is the unique tree maximizing $t$ on $\mathcal{BT}^\ast_n$ for every $n=2^h$, $h\in\mathbb{N}_{\ge0}$.

**Definition (imbalance index).** $t$ is an *imbalance index* if and only if the caterpillar is the unique maximizer of $t$ on $\mathcal{T}^\ast_n$ (respectively $\mathcal{BT}^\ast_n$) for every $n\ge1$, and $T^{fb}_h$ is the unique minimizer of $t$ on $\mathcal{BT}^\ast_{2^h}$ for every $h\ge0$.

Condition 2 is always imposed on binary trees only, even when $t$ is defined on arbitrary trees; the star tree is *not* required to be extremal. Under these axioms the Sackin index $S(T)=\sum_{x\in V_L(T)}\delta_T(x)$, the Colless index and the total cophenetic index are imbalance indices, while the $B_2$ entropy index and the rooted quartet index are balance indices. On binary trees the Colijn–Plazzotta rank is also an imbalance index. Tree shape statistics such as the cherry index or the number of clades of a fixed size fail at least one axiom and are therefore *not* (im)balance indices in this sense.

## Expansion

The two axioms isolate the only two shapes on which the literature agrees: the caterpillar is the least balanced tree for every $n$, and for $n=2^h$ the fully balanced tree is the most balanced. For $n$ not a power of two there is no consensus on the most balanced shape (maximally balanced, greedy-from-the-bottom and Sackin-minimal trees generally differ), so the definition deliberately imposes nothing there. A statistic is classified by checking both uniqueness statements; a statistic that, for example, has the same value on the caterpillar and on another tree fails axiom 1, which is how the cherry index is excluded: for $n=2^h$ with $h\ge3$ its maximum on binary trees is not attained only by the fully balanced tree.

## Sources

- Mareike Fischer, Lina Herbst, Sophie Kersting, Luise Kühn and Kristina Wicke, "Tree Balance Indices: A Comprehensive Survey", Springer, Cham (2023), <https://doi.org/10.1007/978-3-031-39800-1>; numbering as in arXiv:2109.12281: Section 3.1, Definitions 2 and 3, and Sections 3.3–3.4.
