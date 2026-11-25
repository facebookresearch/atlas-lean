# Soundness of the shortest-path search

Let $G$ be a finite directed graph on the vertices
$\{0, \dots, n - 1\}$ and let $s$ and $t$ be vertices. If the breadth-first shortest-path search in
$G$ from $s$ to $t$ returns a list $P$ of vertices, then $P$ is a directed path in $G$ from $s$ to
$t$ without repeated vertices, and breadth-first search in $G$ from $s$ assigns $t$ a distance $d$
such that $P$ has exactly $d + 1$ vertices.
