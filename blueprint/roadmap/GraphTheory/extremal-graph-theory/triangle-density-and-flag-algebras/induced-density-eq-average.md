# Averaging identity for induced densities

For a graph $H$ on $k$ vertices, a graph $G$ on $n$ vertices and $k \le l \le n$, the [induced density](induced-density.md) of $H$ in $G$ is the average of its [induced densities](induced-density-in.md) in the subgraphs of $G$ induced on the $l$-subsets of vertices:

$$p(H, G) = \binom{n}{l}^{-1} \sum_{|L| = l} p(H, G[L]).$$

The proof is the [double count](sum-card-filter-powerset-card.md) of $k$-sets inside $l$-sets together with $\binom{n}{l}\binom{l}{k} = \binom{n}{k}\binom{n-k}{l-k}$. Grouping the $l$-sets $L$ by the isomorphism type $F$ of $G[L]$ turns the identity into the chain rule $p(H, G) = \sum_F p(H, F)\,p(F, G)$ of Razborov's flag algebras, which expresses every density of a small graph as a linear combination of densities of $l$-vertex graphs.

## Sources

- A. A. Razborov, Flag algebras, J. Symbolic Logic 72 (2007), 1239-1282.
