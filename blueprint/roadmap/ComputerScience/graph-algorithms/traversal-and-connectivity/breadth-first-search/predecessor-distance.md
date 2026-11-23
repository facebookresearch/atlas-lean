# A BFS parent is one step closer to the source

Let $G$ be a finite directed graph with
ordered adjacency lists, $s$ a vertex, and $F$ the predecessor forest computed by breadth-first
search with parents from $s$ in $G$. If $F$ records $p$ as the predecessor of a vertex $v$, then
there is a natural number $d$ such that $F$ records distance $d$ for $p$ and distance $d + 1$
for $v$.
