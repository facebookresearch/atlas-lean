# A\*'s predecessor paths are simple and realize its path weights

**A\*'s predecessor paths are simple and realize its path weights.** Let $G$ be a directed graph
on the vertices $\{0, \dots, n-1\}$ with natural edge weights $w$, let $h$ be a consistent heuristic
with natural values and let $s$ be a source vertex. If following the predecessor pointers that A*
from $s$ returns, back from a vertex $v$, yields the vertex list $p$ (listed from $s$ to $v$), then
the path weight $g(v)$ that A* returns for $v$ is finite, $p$ starts at $s$ and ends at $v$,
$G$ has an edge from each vertex of $p$ to the next one, no vertex occurs twice in $p$, and the
weight of $p$ (the sum of $w$ over its consecutive pairs) equals $g(v)$.
