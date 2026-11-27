# Predecessor edges of the DAG shortest-path pass

Let $E$ be a list of integer-weighted
directed edge occurrences on the vertices $\{0, \dots, n-1\}$, let $s$ be a source vertex, and
let $\sigma$ be a topological order of the directed graph obtained from $E$ by forgetting
weights. Suppose the one-pass DAG shortest-path relaxation of $E$ from $s$ in the order $\sigma$
records an edge occurrence $e$ from $u$ to $w$ with weight $c$ as the predecessor of a vertex
$v$. Then $e$ occurs in $E$, $w = v$, and there is an integer $d$ such that the final distance
estimate at $u$ is $d$, the final distance estimate at $v$ is $d + c$, and the position of $u$
in $\sigma$ is less than the position of $v$ in $\sigma$.
