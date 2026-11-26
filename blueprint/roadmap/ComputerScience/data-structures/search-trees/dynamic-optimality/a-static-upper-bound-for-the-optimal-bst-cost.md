# A static upper bound for the optimal BST cost

Fix $n\ge 1$ and an initial [strict binary search tree $T_0$ containing each key in $\{1,\dots,n\}$](tree.md). For a sequence $X$ of $m$ requests from this key set, let $\mathrm{OPT}_{T_0}(X)$ be the [offline minimum cost](is-offline-minimum.md) over plans from $T_0$ in the [binary search tree access model](the-binary-search-tree-access-model.md), including one unit per request. Then

$$m\le \mathrm{OPT}_{T_0}(X)\le m\bigl(\lfloor\log_2 n\rfloor+1\bigr)+O(n),$$

with the additive bound uniform in $T_0$ and $X$. The lower bound holds for every legal plan since it pays at least one per request. For the upper bound, the empty sequence has cost zero. Otherwise, during the first access, reshape $T_0$ into a BST of height $\lfloor\log_2 n\rfloor$ and leave the pointer at its new root. Then serve every request by following its root-to-key path, with no further rotations.

The initial reshaping costs $O(n)$ **primitive operations**, not just $O(n)$ rotations. Sweep the right spine from the root: when the current spine node has a left child, move to that child and rotate it above its parent, lengthening the spine by one; otherwise advance right, or stop if there is no right child. There are at most $n-1$ rotations and at most $n-1$ right advances. This produces the all-right path with the pointer at its last node. Start from that position and reverse the sweep for the target tree: a right advance is undone by a parent move, and a left move followed by a rotation is undone by a right move followed by a rotation. This ends at the target's root with only $O(n)$ additional operations.

## Depends on

- [Strict search trees on a fixed key set](tree.md)
- [The binary search tree access model](the-binary-search-tree-access-model.md)
- [Offline minimum BST cost](is-offline-minimum.md)

## Proof depends on

- [Attainment of the offline minimum](exists-offline-minimum.md)
- [Legal pointer steps](step.md)

## Sources

- J. Iacono, "In pursuit of the dynamic optimality conjecture", in *Space-Efficient Data Structures, Streams, and Algorithms*, LNCS 8066, Springer, 2013; <https://arxiv.org/abs/1306.0207>
