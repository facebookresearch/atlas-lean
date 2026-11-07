# A\* search

**A\* search.** Given a directed graph $G$ on the vertices $\{0, \dots, n-1\}$ with natural
edge weights $w$, a heuristic $h$ with natural values and a source vertex $s$, A* runs Dijkstra's
algorithm from $s$ on the reduced weights $w(u, v) + h(v) - h(u)$ at Dijkstra's cost, and returns
Dijkstra's result (its distances $g'$ and predecessor pointers) together with the path weights
$g(v) = g'(v) + h(s) - h(v)$, where both subtractions are truncated at $0$ and $g(v)$ is infinite
when $g'(v)$ is.

For a consistent heuristic, Dijkstra's distances on the reduced weights are A*'s values
$f = g + h$ shifted by $h(s)$.
