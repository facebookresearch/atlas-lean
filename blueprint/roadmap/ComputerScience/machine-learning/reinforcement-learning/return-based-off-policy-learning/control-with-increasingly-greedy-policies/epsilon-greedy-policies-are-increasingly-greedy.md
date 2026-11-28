# Epsilon-greedy policies with non-increasing epsilon are increasingly greedy

If $(\varepsilon_k)$ is a non-increasing sequence in $[0,1]$ and each $\pi_k$ is the $\varepsilon_k$-greedy policy of $Q_k$, then $(\pi_k)$ is increasingly greedy with respect to $(Q_k)$.

Let $M$ be a Markov decision process with a finite set of states $X$, a finite nonempty set of actions $A$ and transition probabilities $P(x' \mid x,a)$ that are nonnegative and sum to $1$ over $x'$. For a Q-function $Q$ and $\varepsilon \in [0,1]$, an $\varepsilon$-greedy policy of $Q$ fixes at each state $y$ an action $g(y)$ maximizing $Q(y, \cdot)$ (ties broken by any fixed rule) and sets

$$\pi(b \mid y) = (1 - \varepsilon)\, \mathbf{1}\{b = g(y)\} + \frac{\varepsilon}{|A|} .$$

Let $(Q_k)_{k \ge 0}$ be Q-functions and $(\varepsilon_k)_{k \ge 0}$ a non-increasing sequence in $[0,1]$, and let $\pi_k$ be an $\varepsilon_k$-greedy policy of $Q_k$ for each $k$. Then $(\pi_k)$ is increasingly greedy with respect to $(Q_k)$: $P^{\pi_{k+1}}Q_{k+1} \ge P^{\pi_k}Q_{k+1}$ for every $k$.

## Depends on

- [Increasingly greedy sequence of policies](increasingly-greedy-policies.md)
- [Q-function Bellman operator of a stochastic policy](../q-function-bellman-operator.md)

## Proof depends on

- [Increasingly greedy sequence of policies](increasingly-greedy-policies.md)
- [Q-function Bellman operator of a stochastic policy](../q-function-bellman-operator.md)

## Expansion

Write $m(y) = \max_b Q_{k+1}(y,b)$ and $\bar Q(y) = |A|^{-1}\sum_b Q_{k+1}(y,b) \le m(y)$. Then $\sum_b \pi_{k+1}(b \mid y) Q_{k+1}(y,b) = (1-\varepsilon_{k+1}) m(y) + \varepsilon_{k+1}\bar Q(y) \ge (1-\varepsilon_k) m(y) + \varepsilon_k \bar Q(y)$, because $\varepsilon_{k+1} \le \varepsilon_k$ moves weight from $\bar Q$ to the larger $m$; and $(1-\varepsilon_k) m(y) \ge (1-\varepsilon_k) Q_{k+1}(y, g_k(y))$ since $1 - \varepsilon_k \ge 0$, where $g_k$ is the greedy action of $Q_k$. The right side is $\sum_b \pi_k(b \mid y) Q_{k+1}(y,b)$. Averaging over $y \sim P(\cdot \mid x,a)$ gives the claim.

## Sources

- R. Munos, T. Stepleton, A. Harutyunyan, M. G. Bellemare, *Safe and Efficient Off-Policy Reinforcement Learning*, Advances in Neural Information Processing Systems 29 (NIPS 2016), arXiv:1606.02647v2, <https://arxiv.org/abs/1606.02647v2>: Appendix B, Lemma 2 and its proof.
