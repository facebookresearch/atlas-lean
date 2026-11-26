# Greedy satisfies the access lemma

For every assignment of positive weights $w(1), \dots, w(n)$ with $W = \sum_a w(a)$, the total cost of Greedy on an access sequence $X$ of length $m$ is $O\big(m + \sum_{t=1}^m \log \frac{W}{w(x_t)}\big)$ plus an additive term depending only on $n$ and the weights. Consequently Greedy has amortized cost $O(\log n)$ per access and is statically optimal: its cost is $O(m + \mathrm{OPT}_{\mathrm{static}}(X))$, where $\mathrm{OPT}_{\mathrm{static}}$ is the cost of the best fixed BST.

## Proof sketch

Fox defines a potential on the geometric Greedy execution analogous to the splay potential $\sum_a \log(\text{weight of the subtree of } a)$, computed on the staircase structure of points visible from the current row, and shows that the points added in a row telescope against the drop in potential, exactly as in the splay-tree access lemma. Balance follows with uniform weights and static optimality with weights equal to access frequencies.

## Depends on

- [Geometric Greedy (Greedy Future)](geometric-greedy.md)
- [Online arborally satisfying algorithms yield online BSTs](online-geometry-to-online-bst.md)
- [Access lemma for splay trees](../splay-tree/access-lemma-weighted.md)
- [Static optimality of splay trees](../splay-tree/static-optimality.md)

## Proof depends on

- [Geometric Greedy (Greedy Future)](geometric-greedy.md)
- [Online arborally satisfying algorithms yield online BSTs](online-geometry-to-online-bst.md)
- [Access lemma for splay trees](../splay-tree/access-lemma-weighted.md)
- [Static optimality of splay trees](../splay-tree/static-optimality.md)

## Sources

- Kyle Fox, "Upper Bounds for Maximally Greedy Binary Search Trees", WADS (2011), arXiv:1102.4884.
