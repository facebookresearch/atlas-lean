# Shortest path via breadth-first search

Let $G$ be a finite directed graph on the vertices
$\{0, \dots, n - 1\}$ with ordered adjacency lists, and let $s$ be a source and $t$ a sink. Run
breadth-first search from $t$ in the reverse graph of $G$; it labels each vertex $v$ from which $t$
is reachable with the distance from $v$ to $t$ in $G$. If $s$ has no label, the search returns no
path. Otherwise, starting at $s$ with label $d$, take $d$ steps, each time moving to the first
out-neighbour (in adjacency order) whose label is one less than that of the current vertex. The
search returns the list of visited vertices, from $s$ to the last one, if every step succeeds and
the last vertex is $t$, and no path otherwise.
