# The DAG shortest-path pass keeps its source

Let $E$ be a list of integer-weighted
directed edge occurrences on the vertices $\{0, \dots, n-1\}$, let $s$ be a source vertex, and
let $\sigma$ be a topological order of the directed graph obtained from $E$ by forgetting
weights. The result of the one-pass DAG shortest-path relaxation of $E$ from $s$ in the order
$\sigma$ records $s$ as its source.
