# Existence of a reachable negative cycle

Let $E$ be a list of weighted directed edges on
the vertices $0, \dots, n-1$ and $s$ a vertex. Then $E$ has a negative cycle reachable from $s$
when there is a reachable negative cycle witness for $E$ and $s$: a base vertex $b$, a weighted
path in $E$ from $s$ to $b$ that visits no vertex twice, and a nonempty weighted path in $E$ from
$b$ to $b$ whose edge sources are pairwise distinct and whose total weight is negative.
