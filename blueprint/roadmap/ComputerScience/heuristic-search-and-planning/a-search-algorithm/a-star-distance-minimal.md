# A\* with a consistent heuristic is optimal

**A\* with a consistent heuristic is optimal.** Let $G$ be a directed graph on the vertices
$\{0, \dots, n-1\}$ with natural edge weights $w$, let $h$ be a consistent heuristic with natural
values and let $s$ be a source vertex. If the path weight $g(v)$ that A* from $s$ returns for a
vertex $v$ is finite, then $g(v) \le d$ for every weight $d$ of a path in $G$ from $s$ to $v$.
