# Point set of an access sequence and touched set of a BST execution

For an access sequence $X = (x_1, \dots, x_m) \in [n]^m$ its *point set* is $P(X) = \{(x_t, t) : 1 \le t \le m\} \subset \mathbb{Z}^2$, with keys on the horizontal axis and time on the vertical axis. For an execution of a BST algorithm on $X$ in the access model (each access starts at the root, touches a connected subtree containing the root and $x_t$, and may rotate within it), let $T_t$ be the set of keys of nodes touched at time $t$. The *touched set* of the execution is $\{(a, t) : a \in T_t\}$; its size is the cost of the execution.

## Depends on

- [The binary search tree access model](../dynamic-optimality/the-binary-search-tree-access-model.md)

## Sources

- Erik D. Demaine, Dion Harmon, John Iacono, Daniel Kane, Mihai Pătraşcu, "The Geometry of Binary Search Trees", SODA (2009).
