# Adjacency inspections of Prim's algorithm on a simple graph

Let $W$ be a linearly
ordered type with a zero element, let $G$ be a simple graph on the vertices $0, \dots, n-1$, let
$D$ be a directed adjacency structure on the same vertices with adjacency lists $A(u)$, let $w$
assign a weight in $W$ to every unordered pair of vertices, not necessarily distinct, and let
$r$ be a vertex. Suppose that for all vertices $u$ and $v$, $v$ occurs in $A(u)$ exactly when
$u$ and $v$ are adjacent in $G$, and that no list $A(u)$ has repeated entries. Then the number
of adjacency entries inspected by Prim's algorithm on $D$, $w$ and $r$ is twice the number of
edges of $G$.
