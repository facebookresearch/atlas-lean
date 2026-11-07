# Bellman-Ford reconstructed paths are simple and realize the distances

Let $E$ be a list
of integer-weighted directed edges on the vertices $\{0, \dots, n-1\}$ and let $s$ be a vertex.
Suppose Bellman-Ford run on $E$ from $s$ returns distances $d$ together with predecessor edges,
and that reconstructing a path to a vertex $t$ (following predecessor edges back from $t$ for at
most $n$ steps until $s$ is reached) yields the edge sequence $P$. Then $P$ is a walk from $s$
to $t$ along edges of $E$, $d(t)$ is finite and equals the total weight of $P$, the vertex $s$
and the targets of the edges of $P$ are pairwise distinct, and $P$ has fewer than $n$ edges.
