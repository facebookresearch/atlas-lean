# Bellman-Ford reports a negative cycle exactly when one is reachable

Let $E$ be a list of
integer-weighted directed edges on the vertices $\{0, \dots, n-1\}$ and let $s$ be a vertex.
Bellman-Ford run on $E$ from $s$ returns a reachable negative cycle witness if and only if a
negative cycle is reachable from $s$, that is, there are a simple path from $s$ to a vertex $b$
and a nonempty cycle through $b$ along edges of $E$ whose edge sources are pairwise distinct and
whose total weight is negative.
