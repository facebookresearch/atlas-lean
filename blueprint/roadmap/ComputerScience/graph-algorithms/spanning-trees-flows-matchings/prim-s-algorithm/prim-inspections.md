# Number of adjacency inspections in Prim's algorithm

Let $W$ be a linearly ordered type
with a zero element, let $D$ be a directed adjacency structure on the vertices $0, \dots, n-1$
with adjacency lists $A(u)$, let $w$ assign a weight in $W$ to every unordered pair of vertices,
not necessarily distinct, and let $r$ be a vertex. The number of adjacency entries inspected by
Prim's algorithm on $D$, $w$ and $r$ equals the sum of the lengths $|A(u)|$ over all vertices
$u$.
