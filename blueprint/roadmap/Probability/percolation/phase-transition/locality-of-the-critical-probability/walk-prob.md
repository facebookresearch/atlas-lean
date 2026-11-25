# Transition probabilities of simple random walk

Let $G$ be a locally finite simple graph with vertex set $V$ and let $o \in V$. The $k$-step law $p_k(o, \cdot)$ of simple random walk on $G$ started at $o$ is defined recursively by

$$p_0(o, y) = \mathbf{1}[y = o], \qquad p_{k+1}(o, y) = \sum_{x \sim y} \frac{p_k(o, x)}{\deg x},$$

the sum over the neighbours $x$ of $y$; $p_k(o, y)$ is the probability that the walk is at $y$ at time $k$.
