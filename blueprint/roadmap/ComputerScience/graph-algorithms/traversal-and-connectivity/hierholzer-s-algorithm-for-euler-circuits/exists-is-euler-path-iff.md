# Euler path criterion for directed multigraphs

Let $G$ be a directed adjacency graph, read
as a multigraph with one edge per adjacency entry, and let $s$ and $t$ be vertices such that the
source of every edge of $G$ is reachable from $s$. Then $G$ has an Euler path from $s$ to $t$ if
and only if $G$ is semi-balanced for $s$ and $t$: at $s$ one more edge occurrence leaves than
enters, at $t$ one more enters than leaves, and every other vertex is the source of exactly as
many edge occurrences as it is the target of (every vertex, when $s = t$).
