# Alon-Karp-Peleg-West spanning trees of subpolynomial average stretch

Every connected $n$-vertex graph $G$ with $m$ edges and positive edge lengths has a spanning tree $T$ with

$$
\sum_{e \in E} \mathrm{str}^{T, \boldsymbol{\ell}}_e \le m \cdot \exp\bigl(O(\sqrt{\log n \log\log n})\bigr),
$$

and such a tree can be computed in polynomial time.

## Proof sketch

Group edges into length classes that are powers of a parameter $x = \exp(\Theta(\sqrt{\log n\log\log n}))$. Process classes from short to long: in the current contracted graph, partition the vertices into clusters of small radius by growing balls so that only a $1/x$ fraction of the edges of each class is cut, add a shortest-path tree of each cluster, and contract the clusters. An edge whose endpoints are first merged at level $j$ is stretched by $x^{O(j)}$, and the probability bookkeeping over $O(\log n/\log x)$ levels balances to the stated bound.

## Depends on

- [Edge stretch with respect to a spanning tree and edge lengths](edge-stretch-wrt-spanning-tree.md)

## Sources

- Noga Alon, Richard M. Karp, David Peleg, Douglas West, "A Graph-Theoretic Game and Its Application to the k-Server Problem", SIAM J. Comput. 24(1) (1995).
- Michael Elkin, Yuval Emek, Daniel A. Spielman, Shang-Hua Teng, "Lower-Stretch Spanning Trees", STOC (2005), arXiv:cs/0411064.
