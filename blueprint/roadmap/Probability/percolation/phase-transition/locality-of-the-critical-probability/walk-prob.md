# Transition probabilities of simple random walk

Let $G$ be a locally finite simple graph with vertex set $V$ and let $o \in V$. Define $p_k(o, \cdot)$ recursively by

$$p_0(o, y) = \mathbf{1}[y = o], \qquad p_{k+1}(o, y) = \sum_{x \sim y} \frac{p_k(o, x)}{\deg x},$$

the sum over the neighbours $x$ of $y$. This recursion is defined on every locally finite graph. When $o$ has positive degree, $p_k(o, y)$ is the probability that simple random walk on $G$ started at $o$ is at $y$ at time $k$. When $o$ is isolated, $p_0(o, o) = 1$ but $p_k(o, \cdot) = 0$ for every $k > 0$, since the walk has no step to take.
