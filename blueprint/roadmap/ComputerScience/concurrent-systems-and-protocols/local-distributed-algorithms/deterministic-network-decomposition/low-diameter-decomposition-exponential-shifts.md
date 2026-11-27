# Low-diameter decomposition by exponential random shifts

Let $G = (V, E)$ be a simple connected graph with $n$ vertices and maximum degree $\Delta$, whose vertices carry distinct identifiers from $\{1, \dots, n^{O(1)}\}$. For every $\beta \in (0, 1)$, let each vertex $u$ draw an independent shift $\delta_u \sim \mathrm{Exp}(\beta)$ and assign every vertex $v$ to the cluster of a vertex $u$ minimizing $\mathrm{dist}(u, v) - \delta_u$. Then every cluster has strong diameter $O(\log n / \beta)$ with high probability, and every edge has its endpoints in different clusters with probability at most $O(\beta)$. The clustering can be computed in $O(\log n / \beta)$ rounds of CONGEST and in parallel with near-linear work.

## Proof sketch

Subdivide an edge $\{v, w\}$ by its midpoint $m$, at distance $1/2$ from both endpoints. If $v$ and $w$ lie in different clusters, then the two cluster centres both have shifted distance $\mathrm{dist}(\cdot, m) - \delta$ to the midpoint within $1$ of the minimum over all vertices: otherwise the minimizer at $m$ would also be strictly closer, in shifted distance, to the endpoint assigned elsewhere. So the edge is cut only if the smallest and second smallest of the values $\mathrm{dist}(u, m) - \delta_u$ are within $1$ of each other. For arbitrary fixed values $d_u$ and independent $\delta_u \sim \mathrm{Exp}(\beta)$, the memorylessness of the exponential distribution shows that the gap between the smallest and second smallest of $d_u - \delta_u$ exceeds $c$ with probability at least $e^{-\beta c}$, so it is at most $1$ with probability at most $1 - e^{-\beta} \le \beta$; no exact conditional distribution of the gap is needed. A gap of $1$ measured at an endpoint instead of the midpoint would not suffice: on a single edge with $\delta_v = 0.6$ and $\delta_w = 0.1$, $v$ wins at $v$ by $1.5$, yet $w$ wins at $w$. Shifts exceed $O(\log n / \beta)$ with probability $1/\mathrm{poly}(n)$, bounding radii, and clusters are connected since the vertex before $v$ on a shortest path from its centre lies in the same cluster.

## Depends on

- [Network decomposition with weak or strong diameter](network-decomposition-weak-strong-diameter.md)
- [The CONGEST model of distributed computing](the-congest-model.md)

## Sources

- G. L. Miller, R. Peng, S. C. Xu, "Parallel graph decompositions using random shifts", SPAA 2013, arXiv:1307.3692, Algorithm 2 and Lemmas 4.1–4.4.
