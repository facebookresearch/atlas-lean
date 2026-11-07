# Prim's algorithm returns a tree

Let $W$ be a linearly ordered type with a zero element,
let $G$ be a connected simple graph on the vertices $0, \dots, n-1$, let $D$ be a directed
adjacency structure on the same vertices with adjacency lists $A(u)$ such that for all vertices
$u$ and $v$, $v$ occurs in $A(u)$ exactly when $u$ and $v$ are adjacent in $G$, let $w$ assign
a weight in $W$ to every unordered pair of vertices, not necessarily distinct, and let $r$ be a
vertex. Let $T$ be the simple graph on the vertices $0, \dots, n-1$ in which two distinct
vertices are adjacent when one of them is the parent of the other in the output of Prim's
algorithm on $D$, $w$ and $r$. Then $T$ is a tree.
