# Dynamic optimality

In the binary search tree access model, let $\mathrm{OPT}^*(X)$ be the least cost of any BST algorithm, offline and with the best initial tree, that serves the access sequence $X$; it differs from the access model's $\mathrm{OPT}(X)$, whose initial tree is given, by $O(n)$, since any initial tree can be rotated into any other with $O(n)$ rotations. A BST algorithm $A$ is *dynamically optimal* if there is a constant $c$, independent of $n$, such that $\mathrm{cost}_A(X) \le c \cdot \mathrm{OPT}^*(X)$ for every $n$ and every sequence $X$ of at least $n$ accesses to $n$ keys, starting from any initial tree; requiring at least $n$ accesses absorbs the $O(n)$ cost of transforming the initial tree, since $\mathrm{OPT}^*(X)$ is at least the number of accesses. Two questions are attached to this notion, and they are distinct.

- **Splay-tree conjecture** (Sleator and Tarjan, 1985): splay trees are dynamically optimal.
- **Existence of a dynamically optimal online algorithm**: some online BST algorithm is dynamically optimal. The splay-tree conjecture implies it; the converse need not hold.

Tango trees (Demaine, Harmon, Iacono and Pătraşcu, 2007) are $O(\log \log n)$-competitive online BST algorithms. Iacono's 2013 survey records that neither question had been resolved. Guo, Pettie, Skora and Wan (2026 preprint) prove that the Greedy binary search tree is $2^{O(\sqrt{\log \log n})}$-competitive, the first bound $f(n) = o(\log n)$ on its competitive ratio, and record that Greedy is widely conjectured to be $O(1)$-competitive. Their competitive ratio may grow with $n$, while dynamic optimality as defined here requires a constant factor. This page states the notion and both questions and asserts neither.

## Depends on

- [The binary search tree access model](the-binary-search-tree-access-model.md)

## Sources

- J. Iacono, "In pursuit of the dynamic optimality conjecture", in *Space-Efficient Data Structures, Streams, and Algorithms*, LNCS 8066, Springer, 2013; <https://arxiv.org/abs/1306.0207>
- D. D. Sleator and R. E. Tarjan, "Self-adjusting binary search trees", *Journal of the ACM* 32(3):652–686, 1985
- E. D. Demaine, D. Harmon, J. Iacono and M. Pătraşcu, "Dynamic optimality — almost", *SIAM Journal on Computing* 37(1):240–251, 2007
- Y. Guo, S. Pettie, D. Skora and C. Wan, "The Greedy binary search tree is non-trivially competitive", preprint, 2026, arXiv:2608.04410, abstract
