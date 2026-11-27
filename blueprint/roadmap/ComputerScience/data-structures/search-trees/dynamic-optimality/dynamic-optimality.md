# Dynamic optimality

Fix $n \ge 1$, a finite request list $X$ with keys in $\{1,\dots,n\}$, and a [strict binary search tree $T_0$ on that full key set](tree.md). A BST algorithm $A$ specifies a [strategy](strategy.md) for each initial tree. Write $R_A(T_0,X)$ for the normalized cost of its chosen plan, as given by the [serving relation](the-binary-search-tree-access-model.md). Write $\mathrm{OPT}_{T_0}(X)$ for the [offline minimum](is-offline-minimum.md) from that fixed initial tree, and let $\mathrm{OPT}^*(X)=\min_{T_0}\mathrm{OPT}_{T_0}(X)$ be the minimum over initial trees on the same key set.

A BST algorithm $A$ is *dynamically optimal* if there is a constant $c>0$, independent of $n$, such that $R_A(T_0,X)\le c\,\mathrm{OPT}^*(X)$ for every $n\ge 1$, every such initial tree $T_0$, and every sequence $X$ of at least $n$ requests. Allowing the offline plan to choose its initial tree can save only $O(n)$: any two trees on the key set can be joined by a sequence of pointer moves and rotations of that cost, starting and ending at the respective roots. The offline strategy can do this at the beginning of its first access and then carry out the best-start plan. The length condition absorbs this setup cost because $\mathrm{OPT}^*(X)\ge |X|$ under the unit charge per request.

Two questions are attached to this notion, and they are distinct.

- **Splay-tree conjecture** (Sleator and Tarjan, 1985): splay trees are dynamically optimal.
- **Existence of a dynamically optimal online algorithm**: some BST algorithm is dynamically optimal and its strategy for each fixed initial tree satisfies [online prefix dependence](online.md). The splay-tree conjecture implies this existence claim; the converse need not hold.

Tango trees (Demaine, Harmon, Iacono and Pătraşcu, 2007) are $O(\log \log n)$-competitive online BST algorithms. Iacono's 2013 survey records that neither question had been resolved. Guo, Pettie, Skora and Wan (2026 preprint) prove that the Greedy binary search tree is $2^{O(\sqrt{\log \log n})}$-competitive, the first bound $f(n) = o(\log n)$ on its competitive ratio, and record that Greedy is widely conjectured to be $O(1)$-competitive. Their competitive ratio may grow with $n$, while dynamic optimality as defined here requires a constant factor. This page states the notion and both questions and asserts neither.

## Depends on

- [Strict search trees on a fixed key set](tree.md)
- [The binary search tree access model](the-binary-search-tree-access-model.md)
- [Offline minimum BST cost](is-offline-minimum.md)
- [BST access strategies](strategy.md)
- [Online prefix dependence](online.md)

## Proof depends on

- [Attainment of the offline minimum](exists-offline-minimum.md)
- [Legal pointer steps](step.md)

## Sources

- J. Iacono, "In pursuit of the dynamic optimality conjecture", in *Space-Efficient Data Structures, Streams, and Algorithms*, LNCS 8066, Springer, 2013; <https://arxiv.org/abs/1306.0207>
- D. D. Sleator and R. E. Tarjan, "Self-adjusting binary search trees", *Journal of the ACM* 32(3):652–686, 1985
- E. D. Demaine, D. Harmon, J. Iacono and M. Pătraşcu, "Dynamic optimality — almost", *SIAM Journal on Computing* 37(1):240–251, 2007
- Y. Guo, S. Pettie, D. Skora and C. Wan, "The Greedy binary search tree is non-trivially competitive", preprint, 2026, arXiv:2608.04410, abstract
