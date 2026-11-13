# Edge list of an adjacency function

Given a directed adjacency graph $G$ and a function
$R$ assigning to each vertex $u$ a list $R(u)$ of vertices, the edge list of $R$ is the list of
pairs $(u, w)$, one for each entry $w$ of $R(u)$, taken over the vertices $u$ in the order of the
vertex enumeration of $G$ and, for each $u$, in the order of $R(u)$. A repeated entry gives a
repeated pair.
