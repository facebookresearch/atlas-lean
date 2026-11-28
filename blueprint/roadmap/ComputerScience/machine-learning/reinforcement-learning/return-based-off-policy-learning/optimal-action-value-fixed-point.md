# The optimal action value is the unique fixed point of the Q-function optimality operator

The optimal action value $Q^*(x,a) = r(x,a) + \gamma \sum_{x'} P(x' \mid x,a)\, V^*(x')$ is the only Q-function $Q$ with $TQ = Q$, and $\max_a Q^*(x,a) = V^*(x)$ at every state.

Let $M$ be a Markov decision process with a finite nonempty set of states $X$, a finite nonempty set of actions $A$, real rewards $r(x,a)$ and transition probabilities $P(x' \mid x,a)$ that are nonnegative and sum to $1$ over $x'$, and let $0 \le \gamma < 1$. Let $V^*$ be the optimal value and $T$ the Bellman optimality operator on Q-functions. Define the optimal action value

$$Q^*(x,a) = r(x,a) + \gamma \sum_{x'} P(x' \mid x,a)\, V^*(x') .$$

Then $\max_{a} Q^*(x,a) = V^*(x)$ for every state $x$, $TQ^* = Q^*$, and every Q-function $Q$ with $TQ = Q$ equals $Q^*$.

## Depends on

- [Q-function Bellman optimality operator](q-function-bellman-optimality-operator.md)
- [Q-value of an action](../../../heuristic-search-and-planning/value-iteration/q-value.md)
- [Optimal value of a discounted Markov decision process](../../../heuristic-search-and-planning/value-iteration/optimal-value.md)

## Proof depends on

- [Q-function Bellman optimality operator](q-function-bellman-optimality-operator.md)
- [Q-value of an action](../../../heuristic-search-and-planning/value-iteration/q-value.md)
- [Optimal value of a discounted Markov decision process](../../../heuristic-search-and-planning/value-iteration/optimal-value.md)
- [Q-function Bellman operator of a stochastic policy](q-function-bellman-operator.md)

## Expansion

$Q^*(x, \cdot)$ is the vector of Q-values against $V^*$, and the fixed-point equation of $V^*$ says $V^*(x) = \max_a Q^*(x,a)$. Substituting into the definition of $T$ gives $(TQ^*)(x,a) = r(x,a) + \gamma \sum_{x'} P(x' \mid x,a) V^*(x') = Q^*(x,a)$. For uniqueness, $|\max_{a'} f(a') - \max_{a'} g(a')| \le \max_{a'} |f(a') - g(a')|$ gives $\|TQ - TQ'\| \le \gamma \|Q - Q'\|$, so two fixed points coincide.

## Sources

- R. Munos, T. Stepleton, A. Harutyunyan, M. G. Bellemare, *Safe and Efficient Off-Policy Reinforcement Learning*, Advances in Neural Information Processing Systems 29 (NIPS 2016), arXiv:1606.02647v2, <https://arxiv.org/abs/1606.02647v2>: Section 1, equation (2) and the sentence after it (the fixed point of $T$ is $Q^*$, citing Puterman 1994).
- A. Agarwal, N. Jiang, S. M. Kakade, W. Sun, *Reinforcement Learning: Theory and Algorithms*, <https://rltheorybook.github.io/rltheorybook_AJKS_V3.pdf>, Section 1.1.3: Theorem 1.8 (a Q-function equals $Q^*$ if and only if it satisfies the Bellman optimality equations) and equation (0.5) in its proof ($V^*(s) = \max_a Q^*(s,a)$); there $Q^*$ is the action value of an optimal policy, which equals $r + \gamma P V^*$.
