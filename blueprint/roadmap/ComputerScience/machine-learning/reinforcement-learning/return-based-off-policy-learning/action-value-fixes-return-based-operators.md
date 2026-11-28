# The action value is a fixed point of every return-based operator

For any causal trace with finite expected discounted trace mass, and any behaviour policy, the return-based operator built from the target $\pi$ fixes the action value: $\mathcal{R}Q^\pi = Q^\pi$.

Let $M$ be a Markov decision process with a finite set of states $X$, a finite nonempty set of actions $A$, real rewards $r(x,a)$ and transition probabilities $P(x' \mid x,a)$ that are nonnegative and sum to $1$ over $x'$, and let $0 \le \gamma < 1$. Let $\pi$ (target) and $\mu$ (behaviour) be stochastic policies, $Q^\pi$ the action value of $\pi$, and $c$ a causal trace whose expected discounted trace mass $C(x,a)$ is finite at every pair. Then the return-based operator $\mathcal{R}$ of $(\pi, \mu, c)$ satisfies

$$\mathcal{R}Q^\pi = Q^\pi .$$

No admissibility is assumed, and the behaviour policy may give probability zero to the initial action or to actions $\pi$ uses. Uniqueness of the fixed point is a separate matter, proved under admissibility in [Return-based operators contract around the action value](contraction-around-the-action-value.md).

## Depends on

- [Return-based off-policy operator](return-based-off-policy-operator.md)
- [Action value of a stochastic policy](../performance-difference-lemma/stoch-qvalue.md)
- [Causal trace](causal-trace.md)

## Proof depends on

- [The action value is the unique fixed point of the Q-function Bellman operator](q-function-bellman-operator-fixed-point.md)
- [History-dependent randomized policies and trajectory laws](../../../heuristic-search-and-planning/markov-decision-processes/history-dependent-randomized-policies-and-trajectory-laws.md)
- [Return-based off-policy operator](return-based-off-policy-operator.md)
- [Q-function Bellman operator of a stochastic policy](q-function-bellman-operator.md)

## Expansion

Let $\delta^\pi_t = r_t + \gamma (\mathbb{E}_\pi Q^\pi)(x_{t+1}) - Q^\pi(x_t,a_t)$. Given the history $h_t$ and the action $a_t$ (for $t = 0$, given $(x_0,a_0) = (x,a)$), the next state has law $P(\cdot \mid x_t, a_t)$, so $\mathbb{E}[\delta^\pi_t \mid h_t, a_t] = (T^\pi Q^\pi - Q^\pi)(x_t,a_t) = 0$. The weight $\prod_{s=1}^t c_s$ is a function of $(h_t, a_t)$, so the $t$-th term of the series defining $\mathcal{R}Q^\pi - Q^\pi$ is $\gamma^t\, \mathbb{E}[(\prod_{s \le t} c_s)\, \mathbb{E}[\delta^\pi_t \mid h_t, a_t]] = 0$; finite trace mass makes the series well defined.

## Sources

- R. Munos, T. Stepleton, A. Harutyunyan, M. G. Bellemare, *Safe and Efficient Off-Policy Reinforcement Learning*, Advances in Neural Information Processing Systems 29 (NIPS 2016), arXiv:1606.02647v2, <https://arxiv.org/abs/1606.02647v2>: Section 3.1, Theorem 1 (first sentence) and the first paragraph of its proof.
