# The shortest-path search succeeds exactly when the sink is reachable

Let $G$ be a finite
directed graph on the vertices $\{0, \dots, n - 1\}$ and let $s$ and $t$ be vertices. The
breadth-first shortest-path search in $G$ from $s$ to $t$ returns some path if and only if $t$ is
reachable from $s$ in $G$ (every vertex counts as reachable from itself).
