# A stochastic matrix contracts total variation

Let $S$ be a finite set and $P$ a stochastic $S \times S$ matrix (nonnegative entries, rows summing
to $1$). Then for all real vectors $\mu, \nu : S \to \mathbb{R}$ (not necessarily probability
vectors),

$$d_{TV}(\mu P, \nu P) \le d_{TV}(\mu, \nu),$$

where $(\mu P)(y) = \sum_x \mu(x) P(x, y)$ and $d_{TV}(\mu, \nu) = \frac{1}{2} \sum_y |\mu(y) -
\nu(y)|$ is the [total variation distance](tv-dist.md).
