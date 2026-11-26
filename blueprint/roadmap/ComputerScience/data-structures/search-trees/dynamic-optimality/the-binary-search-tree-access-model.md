# The binary search tree access model

Fix $n \ge 1$. The relation $\mathrm{Serves}(T_0, X, P, T_1, c)$ takes an initial tree $T_0$ and a proposed final tree $T_1$, each a [strict search tree containing every key of $\mathrm{Fin}(n)$ exactly once](tree.md), a finite request list $X$ of keys in $\mathrm{Fin}(n)$, a list $P$ of primitive operation lists, and a proposed cost $c \in \mathbb{N}$. A key with index $i$ represents key $i+1$ in $\{1,\dots,n\}$. The relation is false if $P$ and $X$ have different lengths. For empty $X$ and $P$, it holds exactly when $T_1=T_0$ and $c=0$.

Otherwise, the relation holds exactly when the successive operation lists serve their corresponding requests, starting from $T_0$ and passing the resulting tree of each access to the next, with last resulting tree $T_1$. In each access a single pointer starts at the root of the current tree, for free. A move follows an existing edge to the left child, right child, or parent. A rotation promotes the current node over its immediate parent and transfers the intervening subtree to the old parent; the pointer stays on the promoted key. The pointer must visit the requested key at the root or at a later position in the walk, but need not finish there. The cost $c$ must be the sum over accesses of one plus the number of moves and rotations in each access. This additional unit per request normalizes Iacono's primitive count; the relation does not measure time to choose or implement the operations.

## See also

- [Offline minimum BST cost](is-offline-minimum.md) and [attainment of the offline minimum](exists-offline-minimum.md).
- [Online prefix dependence](online.md).

## Sources

- J. Iacono, "In pursuit of the dynamic optimality conjecture", in *Space-Efficient Data Structures, Streams, and Algorithms*, LNCS 8066, Springer, 2013; <https://arxiv.org/abs/1306.0207>, Section 1 (the BST unit-cost primitives).
- Original formalization: R. E. Wilber, "Lower bounds for accessing binary search trees with rotations", *SIAM Journal on Computing* 18(1):56–67, 1989. Iacono, Section 1, credits the model's formalization to Wilber.
