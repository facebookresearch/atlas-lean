# Increasingly greedy sequence of policies

A sequence of stochastic policies $(\pi_k)$ is called increasingly greedy with respect to a sequence of Q-functions $(Q_k)$ when $P^{\pi_{k+1}}Q_{k+1} \ge P^{\pi_k}Q_{k+1}$ for every $k$: each new policy is at least as greedy as the previous one for the new Q-function.

Let $M$ be a Markov decision process with a finite nonempty set of states $X$, a finite nonempty set of actions $A$ and transition probabilities $P(x' \mid x,a)$ that are nonnegative and sum to $1$ over $x'$. Let $(\pi_k)_{k \ge 0}$ be stochastic policies and $(Q_k)_{k \ge 0}$ Q-functions $X \times A \to \mathbb{R}$. The sequence $(\pi_k)$ is defined to be increasingly greedy with respect to $(Q_k)$ when, for every $k \ge 0$ and every pair $(x,a)$,

$$(P^{\pi_{k+1}}Q_{k+1})(x,a) \ge (P^{\pi_k}Q_{k+1})(x,a) .$$

Equivalently $T^{\pi_{k+1}}Q_{k+1} \ge T^{\pi_k}Q_{k+1}$ for any discount $\gamma > 0$. A sufficient condition is the statewise inequality $\sum_b \pi_{k+1}(b \mid y)\, Q_{k+1}(y,b) \ge \sum_b \pi_k(b \mid y)\, Q_{k+1}(y,b)$ at every state $y$; the definition constrains only states reached with positive probability in one step. Policies that put all their mass on maximizing actions of $Q_k$ form an increasingly greedy sequence, and so do $\varepsilon_k$-greedy policies with non-increasing $\varepsilon_k$. Policies concentrated on minimizing actions are the source's example of a sequence that need not have the property. The source also lists softmax policies $\pi_k \propto \exp(\beta_k Q_k)$ with non-decreasing $\beta_k$, but its argument compares with the softmax of $\beta_k Q_{k+1}$ instead of $\pi_k$, and the claim fails for general sequences: with two actions, $\beta_k = \beta_{k+1} = 1$, $Q_{k+1}(y,\cdot) = (1, 0)$ and $Q_k(y,\cdot) = (100, 0)$, the new policy averages $Q_{k+1}(y,\cdot)$ to about $0.73$ and the old one to about $1$, so the inequality fails at any pair that moves to $y$ with probability one.

## Depends on

- [Q-function Bellman operator of a stochastic policy](../q-function-bellman-operator.md)

## Proof depends on

- [Q-function Bellman operator of a stochastic policy](../q-function-bellman-operator.md)

## Expansion

A definition. The equivalence with the Bellman form follows from $T^\pi Q = r + \gamma P^\pi Q$. For greedy policies, $\sum_b \pi_{k+1}(b \mid y) Q_{k+1}(y,b) = \max_b Q_{k+1}(y,b)$, which dominates any average of $Q_{k+1}(y, \cdot)$.

## Sources

- R. Munos, T. Stepleton, A. Harutyunyan, M. G. Bellemare, *Safe and Efficient Off-Policy Reinforcement Learning*, Advances in Neural Information Processing Systems 29 (NIPS 2016), arXiv:1606.02647v2, <https://arxiv.org/abs/1606.02647v2>: Section 3.2, Definition 1 (restated as Definition 2 in Appendix B, with the greedy example and the minimizing counterexample).
