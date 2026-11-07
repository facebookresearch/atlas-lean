# Bellman-Ford succeeds exactly when no negative cycle is reachable

Let $E$ be a list of
integer-weighted directed edges on the vertices $\{0, \dots, n-1\}$ and let $s$ be a vertex.
Bellman-Ford run on $E$ from $s$ returns distances if and only if there is no negative cycle
reachable from $s$, that is, no simple path from $s$ to a vertex $b$ together with a nonempty
cycle through $b$ along edges of $E$ whose edge sources are pairwise distinct and whose total
weight is negative.
