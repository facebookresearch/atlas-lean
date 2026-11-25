# Transition matrix of a stationary policy

For a Markov decision process with states $S$ and a deterministic stationary policy $\mu : S \to A$, the transition matrix of $\mu$ is the $S \times S$ matrix $P_\mu$ with entries $P_\mu(s, s') = p(s, \mu(s), s')$. In a stochastic shortest path problem $S$ is the set of nonterminal states and $P_\mu$ is substochastic.

For a stochastic MDP, the same matrix is the policy kernel of the Dirac (deterministic) stochastic policy of $\mu$: see [The transition matrix of a deterministic policy is its policy kernel](policy-kernel-of-det.md).

## Background

- [Stochastic policies and discounted occupancy](../../machine-learning/reinforcement-learning/stochastic-policies-and-discounted-occupancy/README.md): the policy kernel of a stochastic policy, row-stochastic for stochastic MDPs.
