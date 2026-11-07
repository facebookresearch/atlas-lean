# A\*'s predecessor edges are tight

**A\*'s predecessor edges are tight.** Let $G$ be a directed graph on the vertices
$\{0, \dots, n-1\}$ with natural edge weights $w$, let $h$ be a consistent heuristic with natural
values and let $s$ be a source vertex. If A* from $s$ records $u$ as the predecessor of a vertex
$v$, then $G$ has an edge from $u$ to $v$, the path weights $g(u)$ and $g(v)$ that A* returns are
both finite, and $g(v) = g(u) + w(u, v)$.
