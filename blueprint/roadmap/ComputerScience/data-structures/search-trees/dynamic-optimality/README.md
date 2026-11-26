# Dynamic optimality

A binary search tree algorithm is dynamically optimal if one constant bounds the ratio of its normalized serving cost to the best offline cost, allowing the offline plan to choose the initial tree. The bound must hold for every $n\ge 1$, every initial strict search tree on the full set of $n$ keys, and every request sequence on that set of length at least $n$.

## Idea

Reshaping the tree during one access can make future requests cheaper. An offline plan can choose its rotations with the entire sequence in view; an online strategy must commit to a trace for each request using only the prefix it has seen. The same fixed-initial-tree cost model supplies the offline benchmark, which is then minimized over starting trees. The dynamic-optimality questions ask whether splay trees meet this benchmark within a constant factor and, separately, whether any online strategy does. Defining the access model and its benchmark does not answer either question.

## Statements

- [Dynamic optimality](dynamic-optimality.md)
- [The binary search tree access model](the-binary-search-tree-access-model.md): legal serving plans and their normalized costs.
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
