# Dynamic optimality

Fix $n \ge 1$. The binary search tree access model relates an initial and a final
strict search tree on the same full key set, a finite request list in $\mathrm{Fin}(n)$
(relabeling index $i$ as key $i+1$), a plan, and a natural-number cost. A legal plan
has exactly one operation list per request. A single pointer starts each list at the
current root for free, follows existing child or parent edges or rotates its node over
its immediate parent, and visits the requested key at some point in the walk. A
rotation transfers the intervening subtree to the old parent and keeps the pointer on
the promoted key. Each resulting tree carries over to
the next access, with the last one equal to the specified final tree. The specified
cost must equal one per request plus one per move or rotation. For the empty request
list, only the empty plan with the unchanged tree and zero cost is legal.

## Idea

A request at the root can finish immediately at cost one, without moving the pointer.
To serve a request at a child, the pointer can move there and stop. It can instead
pay for a rotation to bring that key above its parent. That changes the starting tree
for later requests, even though the pointer itself always starts anew at the root.
This distinction is why the cost of a sequence depends on the whole plan, not just
on where each requested key begins in the initial tree.

## Statements

- [The binary search tree access model](the-binary-search-tree-access-model.md)
- [Strict search trees on a fixed key set](tree.md)
- [BST access primitives](primitive.md)
- [Legal pointer steps](step.md)
- [Pointer walks and visited keys](walk.md)
- [Legal single access](access.md)
- [Feasible serving plans](serves-exists.md)
- [Offline minimum BST cost](is-offline-minimum.md)
- [Attainment of the offline minimum](exists-offline-minimum.md)
- [BST access strategies](strategy.md)
- [Online prefix dependence](online.md)
- [A static upper bound for the optimal BST cost](a-static-upper-bound-for-the-optimal-bst-cost.md)
- [Dynamic optimality](dynamic-optimality.md)
