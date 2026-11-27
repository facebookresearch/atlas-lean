# Block rank and cut rank of a matrix

For a matrix $M$ over a field indexed by $V\times V$ and sets $S,T\subseteq V$, the *block rank* is the rank of the submatrix with rows $S$ and columns $T$. The *cut rank* of $S$ is the block rank of $(S,V\setminus S)$; it is symmetric ($S$ and $V\setminus S$ have the same cut rank) when $M$ is symmetric, and submodular as a function of $S$ for every matrix $M$: $\rho(S) + \rho(T) \ge \rho(S \cup T) + \rho(S \cap T)$. For the adjacency matrix of a simple graph over $\mathbb{F}_2$ it is the cut-rank function of the graph.

## Depends on

- [Cut-rank function](../../../GraphTheory/planar-graphs-and-minors/rank-width-and-vertex-minors/cut-rank.md)

## Proof depends on

- [Subadditivity of the rank](../../../Analysis/approximation-theory/low-rank-matrix-recovery/rank-sub-le.md)

## Sources

- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
- S. Oum, "Rank-width and vertex-minors", Journal of Combinatorial Theory, Series B 95(1), 2005: symmetry and submodularity of the cut-rank function.
