# Cover probability of simple random walk

Let $G$ be a simple graph on the vertex set $V = \{1, \dots, n\}$, let $v \in V$ and $m \in \mathbb{N}$. The probability that simple random walk on $G$ started at $v$ visits every vertex within $m$ steps is

$$\operatorname{cov}_G(v, m) = \sum_{w} \prod_{i = 0}^{m-1} \frac{1}{\deg w_i},$$

where the sum runs over all sequences $w = (w_0, w_1, \dots, w_m)$ of vertices with $w_0 = v$, $w_i \sim w_{i+1}$ for every $i < m$, and $\{w_0, \dots, w_m\} = V$.
