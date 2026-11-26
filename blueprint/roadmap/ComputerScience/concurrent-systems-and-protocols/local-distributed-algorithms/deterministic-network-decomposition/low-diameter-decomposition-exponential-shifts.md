# Low-diameter decomposition by exponential random shifts

Let $G = (V, E)$ be a simple connected graph with $n$ vertices and maximum degree $\Delta$, whose vertices carry distinct identifiers from $\{1, \dots, n^{O(1)}\}$. For every $\beta \in (0, 1)$, let each vertex $u$ draw an independent shift $\delta_u \sim \mathrm{Exp}(\beta)$ and assign every vertex $v$ to the cluster of a vertex $u$ minimizing $\mathrm{dist}(u, v) - \delta_u$. Then every cluster has strong diameter $O(\log n / \beta)$ with high probability, and every edge has its endpoints in different clusters with probability at most $O(\beta)$. The clustering can be computed in $O(\log n / \beta)$ rounds of CONGEST and in parallel with near-linear work.

## Proof sketch

The cluster of $v$ is determined by the maximum of $\delta_u - \mathrm{dist}(u, v)$; by memorylessness of the exponential distribution, conditioned on the identity of the maximizer, the gap to the second maximum is again exponentially distributed with rate $\beta$. An edge $\{v, w\}$ is cut only if this gap at $v$ is below $1$, which happens with probability $1 - e^{-\beta} \le \beta$. Shifts exceed $O(\log n / \beta)$ with probability $1/\mathrm{poly}(n)$, bounding radii, and clusters are connected since shortest paths to the centre stay in the cluster.

## Depends on

- [Network decomposition with weak or strong diameter](network-decomposition-weak-strong-diameter.md)
- [The CONGEST model of distributed computing](the-congest-model.md)

## Proof depends on

- [Network decomposition with weak or strong diameter](network-decomposition-weak-strong-diameter.md)

## Sources

- G. L. Miller, R. Peng, S. C. Xu, "Parallel graph decompositions using random shifts", SPAA 2013, arXiv:1307.3692.
