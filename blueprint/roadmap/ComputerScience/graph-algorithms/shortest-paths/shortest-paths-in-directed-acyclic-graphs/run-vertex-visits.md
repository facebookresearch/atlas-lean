# The DAG shortest-path pass is charged one vertex visit per vertex

Let $E$ be a list of
integer-weighted directed edge occurrences on the vertices $\{0, \dots, n-1\}$, let $s$ be a
source vertex, and let $\sigma$ be a topological order of the directed graph obtained from $E$
by forgetting weights. The one-pass DAG shortest-path relaxation of $E$ from $s$ in the order
$\sigma$ is charged exactly $n$ vertex visits.
