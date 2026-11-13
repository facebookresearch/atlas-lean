# DAG shortest-path distances are shortest-path weights

Let $E$ be a list of
integer-weighted directed edges on the vertices $\{0, \dots, n-1\}$ and $s$ a source vertex.
Suppose the DAG shortest-path algorithm on $E$ from $s$ succeeds and returns a finite distance
$d \in \mathbb{Z}$ for a vertex $t$. Then some path from $s$ to $t$ in $E$ has weight $d$, and
every path from $s$ to $t$ in $E$ has weight at least $d$. Here a path from $s$ to $t$ in $E$ is a
list of edges of $E$, each starting where the previous one ends, the first starting at $s$ and
the last ending at $t$ (the empty list when $t = s$), and its weight is the sum of its edge
weights.
