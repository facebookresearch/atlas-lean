# Error identity for return-based operators

The error $\mathcal{R}Q - Q^\pi$ of a return-based operator is an expected discounted sum, from time $1$ on, of trace-weighted differences between the target-policy average of $Q - Q^\pi$ at the current state and the trace-weighted value of $Q - Q^\pi$ at the sampled pair.

Let $M$ be a Markov decision process with a finite nonempty set of states $X$, a finite nonempty set of actions $A$, real rewards $r(x,a)$ and transition probabilities $P(x' \mid x,a)$ that are nonnegative and sum to $1$ over $x'$, and let $0 \le \gamma < 1$. Let $\pi$ (target) and $\mu$ (behaviour) be stochastic policies, $Q^\pi$ the action value of $\pi$, and $c$ a causal trace with finite expected discounted trace mass at every pair. For every Q-function $Q$, with $\Delta Q = Q - Q^\pi$, and every pair $(x,a)$,

$$\mathcal{R}Q(x,a) - Q^\pi(x,a) = \sum_{t \ge 1} \gamma^t\, \mathbb{E}^\mu_{x,a}\Bigl[\Bigl(\prod_{i=1}^{t-1} c_i\Bigr)\bigl((\mathbb{E}_\pi \Delta Q)(x_t) - c_t\, \Delta Q(x_t, a_t)\bigr)\Bigr],$$

where $(\mathbb{E}_\pi \Delta Q)(y) = \sum_b \pi(b \mid y) \Delta Q(y,b)$; the series is absolutely convergent.

## Depends on

- [Return-based off-policy operator](return-based-off-policy-operator.md)
- [Action value of a stochastic policy](../performance-difference-lemma/stoch-qvalue.md)
- [Causal trace](causal-trace.md)
- [Q-function Bellman operator of a stochastic policy](q-function-bellman-operator.md)

## Proof depends on

- [The action value is a fixed point of every return-based operator](action-value-fixes-return-based-operators.md)
- [Return-based off-policy operator](return-based-off-policy-operator.md)
- [Q-function Bellman operator of a stochastic policy](q-function-bellman-operator.md)

## Expansion

Since $\mathcal{R}Q^\pi = Q^\pi$, subtracting the two absolutely convergent series that define $\mathcal{R}Q(x,a)$ and $\mathcal{R}Q^\pi(x,a)$ term by term, the rewards cancel and

$$\mathcal{R}Q(x,a) - Q^\pi(x,a) = \Delta Q(x,a) + \sum_{t \ge 0} \gamma^t\, \mathbb{E}^\mu_{x,a}\Bigl[\Bigl(\prod_{s=1}^t c_s\Bigr)\bigl(\gamma (\mathbb{E}_\pi \Delta Q)(x_{t+1}) - \Delta Q(x_t,a_t)\bigr)\Bigr].$$

Write $W_t = \prod_{s=1}^t c_s \ge 0$, so $W_0 = 1$ and $W_t = W_{t-1} c_t$. Each expectation is a finite sum over histories, so the triangle inequality and $W_t \ge 0$ give, with $|(\mathbb{E}_\pi \Delta Q)(y)| \le \|\Delta Q\|$,

$$\bigl|\mathbb{E}[W_t\, \gamma (\mathbb{E}_\pi \Delta Q)(x_{t+1})]\bigr| \le \gamma \|\Delta Q\|\, \mathbb{E}[W_t], \qquad \bigl|\mathbb{E}[W_t\, \Delta Q(x_t,a_t)]\bigr| \le \|\Delta Q\|\, \mathbb{E}[W_t] .$$

Multiplied by $\gamma^t$ and summed, both bounds are at most $\|\Delta Q\|\, C(x,a) < \infty$, so the series above is the sum of two absolutely convergent series and may be split into them. The $t = 0$ term of the second is $-\Delta Q(x,a)$, because $W_0 = 1$ and $(x_0,a_0) = (x,a)$; it cancels the first term. Shifting the index of the first series by one, which an absolutely convergent series allows, gives $\sum_{t \ge 1} \gamma^t\, \mathbb{E}[W_{t-1} (\mathbb{E}_\pi \Delta Q)(x_t)]$; the second series without its $t = 0$ term is $\sum_{t \ge 1} \gamma^t\, \mathbb{E}[W_{t-1} c_t\, \Delta Q(x_t,a_t)]$, which is subtracted. Combining these two absolutely convergent series term by term gives the identity. Its series is absolutely convergent: the bracket satisfies $|(\mathbb{E}_\pi \Delta Q)(x_t) - c_t\, \Delta Q(x_t,a_t)| \le (1 + c_t)\|\Delta Q\|$, so, with the nonnegative weight $W_{t-1}$,

$$\Bigl|\mathbb{E}\bigl[W_{t-1}\bigl((\mathbb{E}_\pi \Delta Q)(x_t) - c_t\, \Delta Q(x_t,a_t)\bigr)\bigr]\Bigr| \le \|\Delta Q\|\, \bigl(\mathbb{E}[W_{t-1}] + \mathbb{E}[W_t]\bigr),$$

and $\sum_{t \ge 1} \gamma^t (\mathbb{E}[W_{t-1}] + \mathbb{E}[W_t]) = \gamma C(x,a) + C(x,a) - 1 < \infty$. The source proves the identity by first regrouping the rewards; it states the lemma without a summability hypothesis.

## Sources

- R. Munos, T. Stepleton, A. Harutyunyan, M. G. Bellemare, *Safe and Efficient Off-Policy Reinforcement Learning*, Advances in Neural Information Processing Systems 29 (NIPS 2016), arXiv:1606.02647v2, <https://arxiv.org/abs/1606.02647v2>: Section 3.1, Lemma 1; proof in Appendix A.
