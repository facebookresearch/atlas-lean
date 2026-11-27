# Reduced weight

Let $w$ assign a natural number $w(u, v)$ to each pair of vertices and let
$h$ assign a natural number to each vertex. The reduced weight of the pair $(u, v)$ is the
natural number $w(u, v) + h(v) - h(u)$, computed with truncated subtraction, so it is $0$ when
$h(u) > w(u, v) + h(v)$.
