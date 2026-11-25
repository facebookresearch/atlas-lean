# Minimizing the Q-criterion is minimizing the local star BME length of the join

Let $S$ be a finite set of clusters with $|S| \ge 3$ and $D$ a real dissimilarity with $D(u, v) = D(v, u)$ and $D(u, u) = 0$ for all $u, v \in S$. Then for all distinct $a, b \in S$ and all distinct $a', b' \in S$,

$$Q(a, b) \le Q(a', b') \iff L_{ab} \le L_{a'b'},$$

where $Q$ is the [Q-criterion](../neighbor-joining/q-criterion.md) and $L$ the [cherry-tree length](cherry-length.md). This is a local identity on the star of current clusters, not a comparison of partially resolved trees on all taxa.
