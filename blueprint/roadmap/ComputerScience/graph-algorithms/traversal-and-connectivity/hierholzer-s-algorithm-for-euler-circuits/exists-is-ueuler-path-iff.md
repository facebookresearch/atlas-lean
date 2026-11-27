# Euler's theorem for undirected multigraphs

Let $E$ be a finite list of edges of an
undirected multigraph (parallel edges and loops allowed), each given as a pair $(a, b)$, and let
$s$, $t$ be vertices such that the first endpoint $a$ of every edge is reachable from $s$ along
edges of $E$ traversed in either direction. Then $E$ has an Euler path from $s$ to $t$ if and only
if, when $s \ne t$, exactly $s$ and $t$ have odd degree, and, when $s = t$, every vertex has even
degree (a loop counts twice towards the degree).

This is the algorithmic form: the proof shows that Hierholzer's algorithm started at $s$ finds
such a path.
