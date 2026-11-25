# The BME length of a join in terms of the Q-criterion

Let $S$ be a finite set of clusters with $|S| \ge 3$, and let $D$ satisfy $D(u, v) = D(v, u)$ and $D(u, u) = 0$ for all $u, v \in S$. Then for all distinct $a, b \in S$,

$$L_{ab} = \frac{\sum_{u \ne v \in S} D(u, v) + Q(a, b)}{2(|S| - 2)},$$

where $L_{ab}$ is the [cherry-tree length](cherry-length.md) and $Q$ the [Q-criterion](../neighbor-joining/q-criterion.md) on $S$.
