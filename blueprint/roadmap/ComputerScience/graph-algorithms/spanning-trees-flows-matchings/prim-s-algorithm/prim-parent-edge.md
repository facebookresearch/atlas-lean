# Parents returned by Prim's algorithm are adjacency-list neighbors

Let $W$ be a linearly
ordered type with a zero element, let $D$ be a directed adjacency structure on the vertices
$0, \dots, n-1$ with adjacency lists $A(u)$, let $w$ assign a weight in $W$ to every unordered
pair of vertices, not necessarily distinct, and let $r$ be a vertex. For all vertices $u$ and
$v$, if Prim's algorithm on $D$, $w$ and $r$ returns $u$ as the parent of $v$, then $v$ occurs
in $A(u)$.
