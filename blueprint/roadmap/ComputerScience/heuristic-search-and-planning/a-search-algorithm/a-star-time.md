# Cost of A\*

**Cost of A\*.** Let $G$ be a directed graph on the vertices $\{0, \dots, n-1\}$ with natural
edge weights $w$, let $h$ be any heuristic with natural values and let $s$ be a source vertex. In
Dijkstra's dense cost model, which counts the vertex entries inspected by minimum selection and
the adjacency entries inspected by relaxation, A* from $s$ charges exactly $n^2 + m$ events in
total, where $m$ is the number of entries in the adjacency lists of $G$, counting duplicates and
self-loops.
