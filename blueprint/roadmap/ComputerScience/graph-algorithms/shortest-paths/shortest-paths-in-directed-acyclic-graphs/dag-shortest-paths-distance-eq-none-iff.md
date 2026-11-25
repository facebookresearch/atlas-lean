# Unreachable vertices are exactly those at infinite DAG distance

Let $E$ be a list of
integer-weighted directed edges on the vertices $\{0, \dots, n-1\}$ and $s$ a source vertex.
If the DAG shortest-path algorithm on $E$ from $s$ succeeds, then for every vertex $t$ the
returned distance to $t$ is infinite if and only if $t$ is not reachable from $s$ in the directed
graph with an edge $u \to v$ for each edge of $E$ from $u$ to $v$.
