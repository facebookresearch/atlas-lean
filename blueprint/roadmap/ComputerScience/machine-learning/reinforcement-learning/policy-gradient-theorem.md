# Policy gradient theorem

Let a finite discounted MDP have discount $0 \le \gamma < 1$ and start distribution $\mu$, and let
$\theta \mapsto \pi_\theta(a \mid s)$ be a stationary policy class, differentiable in $\theta$ on an open set,
with $\pi_\theta(a \mid s) > 0$ for every $s$, $a$ and $\theta$. With the normalized discounted state
occupancy $d^{\pi_\theta}_\mu(s) = (1-\gamma) \sum_{t \ge 0} \gamma^t \Pr^{\pi_\theta}_\mu(s_t = s)$,

$$\nabla_\theta V^{\pi_\theta}(\mu) = \frac{1}{1-\gamma}\, \mathbb{E}_{s \sim d^{\pi_\theta}_\mu}\, \mathbb{E}_{a \sim \pi_\theta(\cdot \mid s)} \bigl[\nabla_\theta \log \pi_\theta(a \mid s)\, Q^{\pi_\theta}(s, a)\bigr].$$

Without positivity, the same identity holds in the form
$\frac{1}{1-\gamma} \mathbb{E}_{s \sim d^{\pi_\theta}_\mu} \sum_a \nabla_\theta \pi_\theta(a \mid s)\, Q^{\pi_\theta}(s,a)$.

## Depends on

- [Markov decision process](../../heuristic-search-and-planning/value-iteration/mdp.md)
- [Discounted state occupancy of a policy](performance-difference-lemma/occupancy.md)

## Proof depends on

- [Performance difference lemma](performance-difference-lemma/performance-difference.md)

## Related topics

- [Policy gradient theorem for softmax policies](policy-gradients-for-softmax-policies/has-deriv-at-softmax-objective.md)

## Sources

- R. S. Sutton, D. McAllester, S. Singh and Y. Mansour, *Policy gradient methods for reinforcement learning with function approximation*, NIPS 1999, Theorem 1. <https://web.eecs.umich.edu/~baveja/Papers/PolicyGradientNIPS99.pdf>
- A. Agarwal, N. Jiang, S. M. Kakade and W. Sun, *Reinforcement Learning: Theory and Algorithms*, monograph draft, Section 9.1 (policy gradient expressions). <https://rltheorybook.github.io/rltheorybook_ABJKS.pdf>
