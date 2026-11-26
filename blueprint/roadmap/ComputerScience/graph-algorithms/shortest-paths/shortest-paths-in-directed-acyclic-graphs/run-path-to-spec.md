# Paths extracted after topological relaxation are shortest paths

Let $E$ be a list of
integer-weighted directed edges on the vertices $\{0, \dots, n-1\}$, $s$ a source vertex, and
$\sigma$ a topological order of the directed graph with an edge $u \to v$ for each edge of $E$
from $u$ to $v$. After the one-pass relaxation of $E$ from $s$ in the order $\sigma$, suppose
following the predecessor edges back from a vertex $t$ reaches $s$ within $n$ steps, giving the
path $P$. Then $P$ is a path from $s$ to $t$ in $E$, the computed distance to $t$ is finite and
equals the weight of $P$, $P$ has fewer than $n$ edges, and every path from $s$ to $t$ in $E$ has
weight at least the weight of $P$. Here a path from $s$ to $t$ in $E$ is a list of edges of $E$,
each starting where the previous one ends, the first starting at $s$ and the last ending at $t$
(the empty list when $t = s$), and its weight is the sum of its edge weights.
