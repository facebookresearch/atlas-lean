# The transition matrix of a deterministic policy is its policy kernel

For a Markov decision process with finitely many states and actions and a deterministic stationary policy $\mu$, the policy kernel of the Dirac stochastic policy of $\mu$, $P^{\pi}(s, s') = \sum_a \pi(a \mid s)\, p(s, a, s')$ with $\pi(\cdot \mid s)$ the point mass at $\mu(s)$, is the [transition matrix](transition-matrix.md) $P_\mu(s, s') = p(s, \mu(s), s')$.

The policy kernel is row-stochastic when the MDP is stochastic; the transition matrix is used for stochastic shortest path problems, whose transitions are only substochastic.

## Background

- [Stochastic policies and discounted occupancy](../../machine-learning/reinforcement-learning/stochastic-policies-and-discounted-occupancy/README.md): where the policy kernel and the Dirac policy are defined.
