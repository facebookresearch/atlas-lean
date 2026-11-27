# The adjacency matrix acts by summing over labels

Let $V$ and $L$ be finite sets and $\mathrm{rot}$ a [rotation map](rotation-map.md) on $V \times L$, with adjacency matrix $A$. For every $x : V \to \mathbb{R}$ and $v \in V$,

$$(A x)(v) = \sum_{i \in L} x(w_i),$$

where $\mathrm{rot}(v, i) = (w_i, j_i)$, so $w_i$ is the endpoint of the edge with label $i$ at $v$.
