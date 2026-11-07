# Edge list of a directed graph

The edge list of a directed adjacency graph $G$ is the list
of pairs $(u, w)$, one for each entry $w$ of the adjacency list of $u$, taken over the vertices
$u$ in the order of the vertex enumeration of $G$ and, for each $u$, in adjacency-list order. A
repeated adjacency entry gives a repeated pair, so $G$ is read as a multigraph with one edge
occurrence per entry.
