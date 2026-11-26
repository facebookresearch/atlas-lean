# The distance to stationarity does not increase

Let $S$ be a finite set, $P$ a stochastic $S \times S$ matrix (nonnegative entries, rows summing
to $1$) and $\pi : S \to \mathbb{R}$ a vector with $\pi P = \pi$. Then for every start $x \in S$
and every time $t \in \mathbb{N}$,

$$d_{TV}\bigl(P^{t+1}(x, \cdot), \pi\bigr) \le d_{TV}\bigl(P^t(x, \cdot), \pi\bigr),$$

where $d_{TV}(\mu, \nu) = \frac{1}{2} \sum_y |\mu(y) - \nu(y)|$ is the [total variation
distance](tv-dist.md).
