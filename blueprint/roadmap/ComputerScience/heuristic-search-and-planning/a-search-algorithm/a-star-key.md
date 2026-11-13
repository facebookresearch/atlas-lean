# The final keys of A\*

**The final keys of A\*.** Let $G$ be a directed graph on the vertices $\{0, \dots, n-1\}$ with
natural edge weights $w$, let $h$ be a consistent heuristic with natural values and let $s$ be a
source vertex. If the path weight $g(v)$ that A* from $s$ returns for a vertex $v$ is finite, then
the distance $g'(v)$ that Dijkstra's algorithm from $s$ computes for $v$ on the reduced weights
$w(x, y) + h(y) - h(x)$ (subtraction truncated at $0$) is finite as well, and
$g(v) + h(v) = g'(v) + h(s)$; that is, the key $g'(v)$ is A*'s value $f(v) = g(v) + h(v)$ shifted
down by $h(s)$.
