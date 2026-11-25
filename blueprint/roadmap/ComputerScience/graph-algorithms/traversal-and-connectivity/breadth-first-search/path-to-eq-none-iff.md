# Path reconstruction fails exactly at unreachable vertices

Let $G$ be a finite directed
graph given by adjacency lists, and let $s$ and $v$ be vertices. Following the saved parents of the
breadth-first search forest of $G$ from $s$ back from $v$ towards $s$ returns no path if and only
if $v$ is not reachable from $s$ in $G$.
