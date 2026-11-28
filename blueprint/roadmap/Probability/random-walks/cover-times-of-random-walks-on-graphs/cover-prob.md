# Cover probability of simple random walk

Let $G$ be a simple graph on the vertex set $V = \{1, \dots, n\}$, let $v \in V$ and $m \in \mathbb{N}$. Define

$$\operatorname{cov}_G(v, m) = \sum_{w} \prod_{i = 0}^{m-1} \frac{1}{\deg w_i},$$

where the sum runs over all sequences $w = (w_0, w_1, \dots, w_m)$ of vertices with $w_0 = v$, $w_i \sim w_{i+1}$ for every $i < m$, and $\{w_0, \dots, w_m\} = V$: the walks of exactly $m$ steps from $v$ that visit every vertex. When $v$ has positive degree, $\operatorname{cov}_G(v, m)$ is the probability that simple random walk on $G$ started at $v$ visits every vertex within $m$ steps. When $v$ is isolated there is no walk of positive length: on a single vertex, $\operatorname{cov}_G(v, 0) = 1$ but $\operatorname{cov}_G(v, 1) = 0$, although the starting vertex already covers the graph.
