# APPROX-VERTEX-COVER is a 2-approximation

Let $G$ be a simple graph and $L$ a list of
ordered pairs of vertices that lists exactly the edges of $G$, each in at least one orientation:
$u$ and $v$ are adjacent in $G$ for every $(u, v)$ in $L$, and for every edge $uv$ of $G$,
$(u, v)$ or $(v, u)$ is in $L$. Then the cover $C$ that APPROX-VERTEX-COVER returns on $L$ is a
vertex cover of $G$ and $|C| \le 2\tau(G)$, where $\tau(G) \in \mathbb{N} \cup \{\infty\}$ is the
vertex cover number of $G$, the minimum size of a vertex cover of $G$.

## Sources

- CLRS, third edition, Theorem 35.1.
