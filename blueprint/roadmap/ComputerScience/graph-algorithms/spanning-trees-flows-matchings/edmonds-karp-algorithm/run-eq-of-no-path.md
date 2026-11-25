# The iteration stops when there is no augmenting path

Let $c$ be a capacity matrix with
natural-number entries on the vertices $\{0, \dots, n - 1\}$, let $s$ and $t$ be vertices, and let
$f$ be a flow (an integer-valued matrix on pairs of vertices). If the breadth-first shortest-path
search finds no path from $s$ to $t$ in the residual graph of $f$ with respect to $c$, then for
every fuel bound $k$, the augmenting-path iteration started at $f$ with fuel $k$ returns $f$.
