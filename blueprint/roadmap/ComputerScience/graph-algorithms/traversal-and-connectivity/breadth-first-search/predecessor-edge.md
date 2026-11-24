# BFS parents are joined by graph edges

Let $G$ be a finite directed graph with ordered
adjacency lists, $s$ a vertex, and $F$ the predecessor forest computed by breadth-first search
with parents from $s$ in $G$. If $F$ records $p$ as the predecessor of a vertex $v$, then $G$ has
a directed edge from $p$ to $v$, that is, $v$ occurs in the adjacency list of $p$.
