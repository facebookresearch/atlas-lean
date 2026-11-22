# The DAG shortest-path pass gives the source distance zero

Let $E$ be a list of
integer-weighted directed edge occurrences on the vertices $\{0, \dots, n-1\}$, let $s$ be a
source vertex, and let $\sigma$ be a topological order of the directed graph obtained from $E$
by forgetting weights. The one-pass DAG shortest-path relaxation of $E$ from $s$ in the order
$\sigma$ ends with distance estimate $0$ at $s$.

This holds even when edges of negative weight enter $s$.
