# Relaxation count of dense Dijkstra

Let $G$ be a directed graph on the vertices
$0, \dots, n-1$, let $w(u, v)$ be a natural-number weight for every ordered pair of vertices,
and let $s$ be a vertex. The number of adjacency-list entries that Dijkstra's algorithm on $G$
with weights $w$ from source $s$ inspects during relaxation equals the adjacency entry count
of $G$, the total length of all out-neighbour lists.
