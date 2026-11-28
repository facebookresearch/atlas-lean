# Online arborally satisfying algorithms yield online BSTs

For every online arborally satisfying algorithm $\mathcal{G}$ there is an online BST algorithm that starts from the tree built by $\mathrm{MakeTree}$ on all $n$ keys and whose cost on every access sequence $X$ of length $m$, including the $O(n)$ cost of building that initial tree, is $O(\mathrm{cost}_{\mathcal{G}}(X) + m + n)$. In particular Greedy is, up to a constant factor and this additive $O(n)$ initialization, an online BST algorithm.

## Proof sketch

The online algorithm cannot order keys by their unknown next access times, so it keeps keys whose relative order is still undetermined in a *split tree*, a BST supporting $\mathrm{MakeTree}$ on a set of keys and $\mathrm{Split}(x)$, which moves $x$ to the root and deletes it, leaving two split trees; split trees are implemented with $O(n)$ total cost for a $\mathrm{MakeTree}$ and $n$ splits. The BST is a general treap keyed by previous access time whose nodes with tied times are split trees; initially every key is untouched, so the tree is a single split tree on all $n$ keys, built in $O(n)$ time; arboral satisfaction of the output guarantees that the keys of row $t$ can be moved to the root in one root-to-leaf traversal by splitting, at amortized cost $O(1)$ per point of row $t$.

## Depends on

- [Geometric Greedy (Greedy Future)](geometric-greedy.md)
- [Online arborally satisfying algorithms](online-geometric-algorithm.md)
- [The binary search tree access model](../dynamic-optimality/the-binary-search-tree-access-model.md)

## Sources

- Erik D. Demaine, Dion Harmon, John Iacono, Daniel Kane, Mihai Pătraşcu, "The Geometry of Binary Search Trees", SODA (2009).
