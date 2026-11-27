# Mean field equilibrium on a finite state space

A continuum of identical players each choose a state $y$ of a finite set $Q$; a player in state $y$
pays $F(y, m)$ when the population is distributed according to the probability vector $m$. A
probability vector $m$ is a mean field equilibrium if

$$\sum_y F(y, m)\, m(y) \le \sum_y F(y, m)\, m'(y) \quad \text{for every probability vector } m',$$

that is $\int F(y, m)\, dm(y) = \inf_{m'} \int F(y, m)\, dm'(y)$: given the crowd, no player
gains by deviating. Equivalently, $m$ is [supported on the minimisers](is-mean-field-equilibrium-iff.md)
of $F(\cdot, m)$.

In Lions' lectures such equilibria arise as limits of Nash equilibria of symmetric $N$-player games
with costs $F(x_i, \frac{1}{N-1}\sum_{j \ne i} \delta_{x_j})$ (Cardaliaguet, Theorems 2.4 and 2.7), where
$Q$ is a compact metric space; here $Q$ is finite.

## Background

- [Wardrop equilibrium](../selfish-routing-and-the-price-of-anarchy/is-wardrop.md): a
  single-commodity Wardrop flow, normalised to unit demand, is a mean field equilibrium in which the
  states are paths and the cost of a path is its latency under the flow.

## Sources

- J.-M. Lasry and P.-L. Lions, "Mean field games", Japan. J. Math. 2 (2007), 229–260.
- P. Cardaliaguet, *Notes on Mean Field Games (from P.-L. Lions' lectures at Collège de France)*, version of 27 September 2013, §2.2, equation (4).
