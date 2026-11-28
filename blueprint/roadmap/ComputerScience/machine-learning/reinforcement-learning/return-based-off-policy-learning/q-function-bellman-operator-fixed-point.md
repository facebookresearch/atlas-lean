# The action value is the unique fixed point of the Q-function Bellman operator

The action value $Q^\pi$ of a stochastic policy is the only Q-function $Q$ with $T^\pi Q = Q$; equivalently, $Q^\pi = \sum_{t \ge 0} \gamma^t (P^\pi)^t r = (I - \gamma P^\pi)^{-1} r$.

Let $M$ be a Markov decision process with a finite nonempty set of states $X$, a finite nonempty set of actions $A$, real rewards $r(x,a)$ and transition probabilities $P(x' \mid x,a)$ that are nonnegative and sum to $1$ over $x'$, and let $0 \le \gamma < 1$. Let $\pi$ be a stochastic policy, $V^\pi$ its value, and

$$Q^\pi(x,a) = r(x,a) + \gamma \sum_{x'} P(x' \mid x,a)\, V^\pi(x')$$

its action value. Let $P^\pi$ and $T^\pi Q = r + \gamma P^\pi Q$ be the operators on Q-functions $Q : X \times A \to \mathbb{R}$. Then:

1. $T^\pi Q^\pi = Q^\pi$;
2. every Q-function $Q$ with $T^\pi Q = Q$ equals $Q^\pi$;
3. the matrix $I - \gamma P^\pi$ is invertible, the series $\sum_{t \ge 0} \gamma^t (P^\pi)^t$ is absolutely convergent with sum $(I - \gamma P^\pi)^{-1}$ (the Neumann series of the nonnegative matrix $\gamma P^\pi$, whose row sums equal $\gamma < 1$), and $Q^\pi = \sum_{t \ge 0} \gamma^t (P^\pi)^t r$.

Item 3 is the form in which the source defines $Q^\pi$; items 1 and 2 identify that definition with the action value defined from $V^\pi$.

## Depends on

- [Q-function Bellman operator of a stochastic policy](q-function-bellman-operator.md)
- [Action value of a stochastic policy](../performance-difference-lemma/stoch-qvalue.md)
- [Value of a stochastic policy](../stochastic-policies-and-discounted-occupancy/stoch-value.md)
- [Neumann series for the Leontief inverse when row sums are below one](../../../../Economics/general-equilibrium/leontief-input-output-model/has-sum-pow-of-row-sum-lt-one.md)

## Proof depends on

- [Q-function Bellman operator of a stochastic policy](q-function-bellman-operator.md)
- [Action value of a stochastic policy](../performance-difference-lemma/stoch-qvalue.md)
- [Bellman consistency for stochastic policies](../stochastic-policies-and-discounted-occupancy/stoch-value-eq.md)
- [Neumann series for the Leontief inverse when row sums are below one](../../../../Economics/general-equilibrium/leontief-input-output-model/has-sum-pow-of-row-sum-lt-one.md)

## Expansion

By Bellman consistency, $V^\pi(x') = \sum_{a'} \pi(a' \mid x')\, Q^\pi(x',a') = (\mathbb{E}_\pi Q^\pi)(x')$; substituting into the definition of $Q^\pi$ gives $Q^\pi = r + \gamma P^\pi Q^\pi$. Every row of $P^\pi$ is a probability vector, so $\|P^\pi f\| \le \|f\|$ and $\|T^\pi Q - T^\pi Q'\| \le \gamma \|Q - Q'\|$; two fixed points $Q, Q'$ then satisfy $\|Q - Q'\| \le \gamma \|Q - Q'\|$, hence coincide. The matrix $\gamma P^\pi$ has nonnegative entries and row sums $\gamma < 1$, so its power series converges to $(I - \gamma P^\pi)^{-1}$; absolute convergence holds since the $t$-th term has operator norm $\gamma^t$. Finally $(I - \gamma P^\pi) Q^\pi = r$ by item 1.

## Sources

- R. Munos, T. Stepleton, A. Harutyunyan, M. G. Bellemare, *Safe and Efficient Off-Policy Reinforcement Learning*, Advances in Neural Information Processing Systems 29 (NIPS 2016), arXiv:1606.02647v2, <https://arxiv.org/abs/1606.02647v2>: Section 1, equation (1) and the sentence after it ($T^\pi Q^\pi = Q^\pi = (I - \gamma P^\pi)^{-1} r$).
