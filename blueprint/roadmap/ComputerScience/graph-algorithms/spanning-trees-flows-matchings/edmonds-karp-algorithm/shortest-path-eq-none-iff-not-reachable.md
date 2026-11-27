# The shortest-path search fails exactly when the sink is unreachable

Let $G$ be a finite
directed graph on the vertices $\{0, \dots, n - 1\}$ and let $s$ and $t$ be vertices. The
breadth-first shortest-path search in $G$ from $s$ to $t$ returns no path if and only if $t$ is not
reachable from $s$ in $G$.
