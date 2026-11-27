# Reconstructed BFS paths are shortest paths

Let $G$ be a finite directed graph given by
adjacency lists, let $s$ and $v$ be vertices, and suppose that following the saved parents of the
breadth-first search forest of $G$ from $s$ back from $v$ returns a list $P$ of vertices. Then $P$
starts at $s$ and ends at $v$, each vertex of $P$ after the first has the preceding vertex as its
saved parent, $G$ has an edge from each vertex of $P$ to the next, no vertex occurs twice in $P$,
breadth-first search from $s$ reports a distance $d$ for $v$ and $P$ has $d + 1$ vertices, and
every list of vertices from $s$ to $v$ such that $G$ has an edge from each of its vertices to the
next has at least as many vertices as $P$.
