# A static upper bound for the optimal BST cost

In the binary search tree access model on keys $\{1, \dots, n\}$ with $n \ge 1$, every access sequence $X$ of length $m$ satisfies $\mathrm{OPT}(X) \le m(\lfloor \log_2 n \rfloor + 1) + O(n)$, where the $O(n)$ term pays for transforming the initial tree into a perfectly balanced tree by rotations; after that, every access follows a root-to-node path of length at most $\lfloor \log_2 n \rfloor$ and no rotation is performed. Every BST algorithm $A$ satisfies $R_A(X) \ge m$, since each access costs at least $1$. The $O(n)$ bound holds because at most $n - 1$ rotations turn any binary search tree on $n$ keys into a right path (each right rotation at a node of the right spine that has a left child lengthens the spine by one), and reversing the same process for the target tree turns the right path into a perfectly balanced tree with at most $n - 1$ further rotations.

## Depends on

- [The binary search tree access model](the-binary-search-tree-access-model.md)

## Sources

- J. Iacono, "In pursuit of the dynamic optimality conjecture", in *Space-Efficient Data Structures, Streams, and Algorithms*, LNCS 8066, Springer, 2013; <https://arxiv.org/abs/1306.0207>
