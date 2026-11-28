# Q-function Bellman optimality operator

The Bellman optimality operator on Q-functions is defined by replacing the policy average of the next action with a maximum: $(TQ)(x,a) = r(x,a) + \gamma \sum_{x'} P(x' \mid x,a) \max_{a'} Q(x',a')$.

Let $M$ be a Markov decision process with a finite set of states $X$, a finite nonempty set of actions $A$, real rewards $r(x,a)$ and transition probabilities $P(x' \mid x,a)$ that are nonnegative and sum to $1$ over $x'$, and let $0 \le \gamma < 1$. For a Q-function $Q : X \times A \to \mathbb{R}$ define

$$(TQ)(x,a) = r(x,a) + \gamma \sum_{x' \in X} P(x' \mid x,a) \max_{a' \in A} Q(x',a') .$$

The maximum exists because $A$ is finite and nonempty. Since a policy average of $Q(x', \cdot)$ never exceeds its maximum, $T^\pi Q \le TQ$ for every stochastic policy $\pi$, with equality when every $\pi(\cdot \mid x')$ is supported on the maximizing actions of $Q(x', \cdot)$; in this sense $TQ = r + \gamma \max_\pi P^\pi Q$, the maximum being taken at every pair and attained.

## Depends on

- [Markov decision process](../../../heuristic-search-and-planning/value-iteration/mdp.md)
- [Stochastic Markov decision process](../../../heuristic-search-and-planning/value-iteration/stochastic.md)
- [Q-function Bellman operator of a stochastic policy](q-function-bellman-operator.md)

## Proof depends on

- [Q-function Bellman operator of a stochastic policy](q-function-bellman-operator.md)

## Expansion

A definition. The comparison with $T^\pi$: $(\mathbb{E}_\pi Q)(x') = \sum_{a'} \pi(a' \mid x') Q(x',a') \le \max_{a'} Q(x',a')$, with equality exactly when $\pi(\cdot \mid x')$ charges only maximizers; multiply by $\gamma P(x' \mid x,a) \ge 0$ and sum.

## Sources

- R. Munos, T. Stepleton, A. Harutyunyan, M. G. Bellemare, *Safe and Efficient Off-Policy Reinforcement Learning*, Advances in Neural Information Processing Systems 29 (NIPS 2016), arXiv:1606.02647v2, <https://arxiv.org/abs/1606.02647v2>: Section 1, equation (2).
