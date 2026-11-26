# Network decomposition with weak or strong diameter

Let $G = (V, E)$ be a simple connected graph with $n$ vertices and maximum degree $\Delta$, whose vertices carry distinct identifiers from $\{1, \dots, n^{O(1)}\}$. A $(C, D)$-network decomposition is a partition of $V$ into clusters together with a colouring of the clusters by $C$ colours such that clusters of the same colour are non-adjacent (no edge joins two distinct clusters of the same colour) and every cluster has diameter at most $D$. It has strong diameter $D$ if each cluster $S$ induces a connected subgraph $G[S]$ of diameter at most $D$, and weak diameter $D$ if $\mathrm{dist}_G(u, v) \le D$ for all $u, v$ in the same cluster. For a power graph $G^k$ (vertices adjacent when at distance at most $k$ in $G$), a decomposition of $G^k$ separates same-coloured clusters by distance greater than $k$ in $G$.

## Depends on

- [The LOCAL model](../../distributed-execution-models/the-local-model.md)
- [The CONGEST model of distributed computing](the-congest-model.md)

## Sources

- N. Linial, M. Saks, "Low diameter graph decompositions", Combinatorica 13(4) (1993).
- B. Awerbuch, A. V. Goldberg, M. Luby, S. A. Plotkin, "Network decomposition and locality in distributed computation", FOCS 1989.
