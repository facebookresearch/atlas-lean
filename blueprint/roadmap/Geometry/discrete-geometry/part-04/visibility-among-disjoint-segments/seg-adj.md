# Adjacency in the segment visibility graph

Let $e_0, \dots, e_{2m-1} \in \mathbb{R}^2$ be the endpoints of segments $s_k = [e_{2k}, e_{2k+1}]$, $0 \le k < m$. Endpoint indices $i$ and $j$ are adjacent in the segment visibility graph when $i \ne j$ and either

- $\lfloor i/2 \rfloor = \lfloor j/2 \rfloor$, so $e_i$ and $e_j$ are the two endpoints of one segment, or
- the open segment $(e_i, e_j)$ is disjoint from every segment $s_k$.

So two endpoints see each other only if the segment joining them does not pass through another endpoint or touch any segment.
