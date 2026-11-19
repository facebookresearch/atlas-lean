# Dense Dijkstra's algorithm

Let $G$ be a directed graph on the vertices $0, \dots, n-1$
given by a fixed enumeration of its vertices and adjacency lists, let $w(u, v) \in \mathbb{N}$ be
a weight for each ordered pair of vertices, and let $s$ be a source vertex. The algorithm starts
with $d(s) = 0$, $d(v) = \infty$ for $v \ne s$, no predecessors and no settled vertices, and runs
$n$ rounds. In each round it scans all vertices in the order of the enumeration of $G$ and
selects the first unsettled vertex $u$ in that order whose value $d(u)$ is minimal among
unsettled vertices; if every vertex is settled the round does nothing. Otherwise it marks $u$
settled and, for each entry $v$ of the adjacency list of $u$ in order, if $v$ is unsettled,
$d(u)$ is finite and $d(u) + w(u, v) < d(v)$, it sets $d(v) := d(u) + w(u, v)$ and makes $u$ the
predecessor of $v$. The result is $s$ together with the final distances and predecessors. The
cost charges one minimum-selection step for each vertex inspected during selection and one
relaxation step for each adjacency entry inspected during relaxation.
