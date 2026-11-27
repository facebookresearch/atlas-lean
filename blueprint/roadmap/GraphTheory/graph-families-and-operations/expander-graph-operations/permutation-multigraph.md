# Regular multigraph of a family of permutations (Schreier-type graph)

Given a finite set $V$ and a finite family of permutations $\sigma_k$ of $V$, $k \in K$, the permutation multigraph is the $2|K|$-regular multigraph on $V$ with labels $K \times \{+, -\}$: at a vertex $v$, the label $(k, +)$ leads to $\sigma_k(v)$ and the label $(k, -)$ leads to $\sigma_k^{-1}(v)$, and the rotation map pairs $(v, (k, +))$ with $(\sigma_k(v), (k, -))$. When the $\sigma_k$ are the actions of the generators of a group action, this is the Schreier graph for the generators and their inverses. For every $S \subseteq V$ the number of darts from $S$ to $V \setminus S$ equals $2 \sum_{k} |\{v \in S : \sigma_k(v) \notin S\}|$.

## Depends on

- [Rotation map of a regular multigraph](../zig-zag-product-and-explicit-expanders/rotation-map.md)
- [Spectral expansion, second eigenvalue and edge expansion of a regular multigraph](spectral-expansion-second-eigenvalue-and-edge-expansion.md)

## Sources

- S. Hoory, N. Linial, A. Wigderson, "Expander Graphs and Their Applications", Bulletin of the American Mathematical Society, 2006.
