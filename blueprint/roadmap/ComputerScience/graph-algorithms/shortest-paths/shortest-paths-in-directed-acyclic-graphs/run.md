# One-pass DAG shortest-path relaxation

Let $E$ be a list of integer-weighted directed
edge occurrences on the vertices $\{0, \dots, n-1\}$, let $s$ be a source vertex, and let
$\sigma$ be a topological order of the directed graph obtained from $E$ by forgetting weights.
The relaxation starts from distance estimate $0$ at $s$, infinite estimates at every other
vertex and no predecessor edges. It then takes the vertices $u$ of $\sigma$ in turn and relaxes
each occurrence $e$ in $E$ from $u$ to some $v$ with weight $c$, in the order of $E$: if the
estimate $d$ at $u$ is finite and the estimate at $v$ is infinite or greater than $d + c$, it
sets the estimate at $v$ to $d + c$ and the predecessor of $v$ to $e$. The result records $s$ as
its source together with the final estimates and predecessors. Its cost counts one vertex visit
per vertex of $\sigma$, one edge relaxation per occurrence relaxed, and one distance update per
estimate set.

The original edge occurrences are retained, so every parallel occurrence is checked. The proof
that $\sigma$ is a topological order is not used by the computation.
