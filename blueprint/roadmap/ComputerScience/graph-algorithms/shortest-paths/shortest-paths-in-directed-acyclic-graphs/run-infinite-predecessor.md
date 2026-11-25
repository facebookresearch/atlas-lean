# Unreached vertices have no DAG shortest-path predecessor

Let $E$ be a list of
integer-weighted directed edge occurrences on the vertices $\{0, \dots, n-1\}$, let $s$ be a
source vertex, and let $\sigma$ be a topological order of the directed graph obtained from $E$
by forgetting weights. If the one-pass DAG shortest-path relaxation of $E$ from $s$ in the
order $\sigma$ ends with an infinite distance estimate at a vertex $v$, then it records no
predecessor edge for $v$.
