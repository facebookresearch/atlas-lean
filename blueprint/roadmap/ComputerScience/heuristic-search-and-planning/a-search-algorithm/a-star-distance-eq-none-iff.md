# A\* leaves exactly the unreachable vertices at infinity

**A\* leaves exactly the unreachable vertices at infinity.** Let $G$ be a directed graph on the
vertices $\{0, \dots, n-1\}$ with natural edge weights $w$, let $h$ be any heuristic with natural
values and let $s$ be a source vertex. The path weight $g(v)$ that A* from $s$ returns for a vertex
$v$ is infinite if and only if $v$ is not reachable from $s$ in $G$.
