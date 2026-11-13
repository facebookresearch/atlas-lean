# Phases are maximal

Suppose the partner array describes a matching and $d$ is the earliest
round such that round $d + 1$ of the alternating breadth-first search reaches an unmatched right
vertex. Then for every $k$, every augmenting path $Q$ at level $k$ with exactly $d + 1$ pairs
shares a vertex with some path $P$ of the phase: some pair of $Q$ has its left vertex among the
left vertices of $P$ or its right vertex among the right vertices of $P$.

Every augmenting path has at least $d + 1$ pairs, so these are the shortest augmenting paths, and
the phase's vertex-disjoint shortest augmenting paths form a maximal set, as Hopcroft and Karp
require.
