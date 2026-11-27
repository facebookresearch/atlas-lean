# Reduced weights telescope along paths

Let $G$ be a directed graph on the vertices
$\{0, \dots, n-1\}$ with natural edge weights $w$, let $h$ be a consistent heuristic with natural
values, and let $w_h(x, y) = w(x, y) + h(y) - h(x)$ be the reduced weight, with the subtraction
truncated at $0$. For all vertices $u$ and $v$ and every nonempty list of vertices
$v_0, v_1, \dots, v_k$ with $v_0 = u$, $v_k = v$ and an edge of $G$ from each $v_i$ to $v_{i+1}$,
the sum of $w_h(v_i, v_{i+1})$ over $i < k$, plus $h(u)$, equals the sum of $w(v_i, v_{i+1})$
over $i < k$, plus $h(v)$.
