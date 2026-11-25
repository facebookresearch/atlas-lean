# The convergence theorem

Let $S$ be a finite set and $P$ a stochastic $S \times S$ matrix (nonnegative entries, rows
summing to $1$) that is primitive: some power $P^k$ with $k > 0$ has all entries strictly
positive (for a stochastic matrix, irreducible and aperiodic). Let $\pi$ be a stationary
distribution: $\pi(y) \ge 0$, $\sum_y \pi(y) = 1$ and $\pi P = \pi$. Then there are real
numbers $C$ and $\alpha$ with $0 \le \alpha < 1$ such that for every $n \in \mathbb{N}$ and every
start $x \in S$,

$$d_{TV}\bigl(P^n(x, \cdot), \pi\bigr) \le C \alpha^n,$$

where $d_{TV}(\mu, \nu) = \frac{1}{2} \sum_y |\mu(y) - \nu(y)|$ is the [total variation
distance](../mixing-times-of-markov-chains/tv-dist.md).

## Sources

- D. A. Levin, Y. Peres and E. L. Wilmer, *Markov Chains and Mixing Times*, 2nd ed., American
  Mathematical Society, 2017, Theorem 4.9.
