# Extracted DAG shortest paths are shortest paths

Let $E$ be a list of integer-weighted
directed edges on the vertices $\{0, \dots, n-1\}$ and $s$ a source vertex. Suppose the DAG
shortest-path algorithm on $E$ from $s$ succeeds, and following its predecessor edges back from a
vertex $t$ reaches $s$ within $n$ steps, giving the path $P$. Then $P$ is a path from $s$ to $t$
in $E$, the returned distance to $t$ is finite and equals the weight of $P$, $P$ has fewer than
$n$ edges, and every path from $s$ to $t$ in $E$ has weight at least the weight of $P$. Here a
path from $s$ to $t$ in $E$ is a list of edges of $E$, each starting where the previous one ends,
the first starting at $s$ and the last ending at $t$ (the empty list when $t = s$), and its weight
is the sum of its edge weights.
