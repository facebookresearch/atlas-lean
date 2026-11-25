# Ball of radius $r$ in a graph

Let $G$ be a simple graph with vertex set $V$, let $v \in V$ and $r \in \mathbb{N}$. The closed ball $B_G(v, r)$ is the induced subgraph of $G$ on the vertex set

$$\{w \in V : d_G(v, w) \le r\},$$

where $d_G$ is the graph distance. Here $d_G(v, w) = 0$ when $w$ is not reachable from $v$, so for a disconnected graph the ball also contains every vertex outside the connected component of $v$.
