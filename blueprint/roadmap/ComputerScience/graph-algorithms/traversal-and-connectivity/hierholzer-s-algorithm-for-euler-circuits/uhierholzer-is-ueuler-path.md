# Undirected Hierholzer's algorithm finds Euler paths

Let $E$ be a list of undirected edges
(ordered pairs of vertices) and $s$, $t$ vertices such that exactly $s$ and $t$ have odd degree in
$E$ (no vertex has odd degree when $s = t$), and suppose the first endpoint of every edge of $E$ is
reachable from $s$ through edges of $E$. Then the vertex sequence returned by the undirected
Hierholzer algorithm on $E$ from $s$ is an Euler path of $E$ from $s$ to $t$.
