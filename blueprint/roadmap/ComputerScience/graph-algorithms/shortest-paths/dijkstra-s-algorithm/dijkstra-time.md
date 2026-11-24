# Running time of dense Dijkstra

Let $G$ be a directed graph on the vertices
$0, \dots, n-1$ given by adjacency lists, let $w(u, v) \in \mathbb{N}$ be a weight for each
ordered pair of vertices, and let $s$ be a vertex. For dense Dijkstra from $s$, the number of
vertex entries inspected by minimum selection plus the number of adjacency entries inspected by
relaxation is exactly $n^2 + m$, where $m$ is the number of adjacency-list entries of $G$,
counting duplicates and self-loops.
