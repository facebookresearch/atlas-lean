# State-action contraction coefficient of a return-based operator

For an admissible causal trace, the error of the return-based operator at a pair is at most $\eta(x,a) = 1 - (1-\gamma)C(x,a)$ times $\|Q - Q^\pi\|$, where $C(x,a)$ is the expected discounted trace mass; the coefficient $\eta(x,a)$ lies in $[0, \gamma]$.

Let $M$ be a Markov decision process with a finite set of states $X$, a finite nonempty set of actions $A$, real rewards $r(x,a)$ and transition probabilities $P(x' \mid x,a)$ that are nonnegative and sum to $1$ over $x'$, and let $0 \le \gamma < 1$. Let $\pi$ (target) and $\mu$ (behaviour) be stochastic policies, $Q^\pi$ the action value of $\pi$, $c$ a causal trace admissible for $(\pi,\mu)$, $C(x,a) = \sum_{t \ge 0} \gamma^t\, \mathbb{E}^\mu_{x,a}[\prod_{s=1}^t c_s]$ and $\mathcal{R}$ the return-based operator. Then for every Q-function $Q$ and pair $(x,a)$,

$$\mathcal{R}Q(x,a) - Q^\pi(x,a) = \sum_{(y,b) \in X \times A} w_{y,b}\, (Q - Q^\pi)(y,b), \qquad w_{y,b} = \sum_{t \ge 1} \gamma^t\, \mathbb{E}^\mu_{x,a}\Bigl[\Bigl(\prod_{i=1}^{t-1} c_i\Bigr)\bigl(\pi(b \mid x_t) - \mu(b \mid x_t)\, c_t(b, h_t)\bigr)\mathbf{1}\{x_t = y\}\Bigr],$$

with weights $w_{y,b} \ge 0$ (depending on $(x,a)$) whose sum is $\eta(x,a) = 1 - (1-\gamma)C(x,a) \in [0, \gamma]$. Consequently

$$|\mathcal{R}Q(x,a) - Q^\pi(x,a)| \le \eta(x,a)\, \|Q - Q^\pi\| .$$

The coefficient equals $\gamma$ when $c_1 = 0$ almost surely (the trace is cut at once) and is small when the traces stay close to $1$ for many steps.

## Depends on

- [Return-based off-policy operator](return-based-off-policy-operator.md)
- [Causal trace](causal-trace.md)
- [Action value of a stochastic policy](../performance-difference-lemma/stoch-qvalue.md)

## Proof depends on

- [Error identity for return-based operators](error-identity-for-return-based-operators.md)
- [Admissible trace products have mean at most one](admissible-trace-products-mean-at-most-one.md)
- [History-dependent randomized policies and trajectory laws](../../../heuristic-search-and-planning/markov-decision-processes/history-dependent-randomized-policies-and-trajectory-laws.md)
- [Causal trace](causal-trace.md)
- [Return-based off-policy operator](return-based-off-policy-operator.md)

## Expansion

In the error identity, condition the $t$-th term on $h_t$: given $h_t$ the action $a_t$ has law $\mu(\cdot \mid x_t)$, so $\mathbb{E}[c_t\, \Delta Q(x_t,a_t) \mid h_t] = \sum_b \mu(b \mid x_t)\, c_t(b,h_t)\, \Delta Q(x_t, b)$, while $\prod_{i<t} c_i$ is a function of $h_t$. This gives the weights; admissibility makes them nonnegative. Summing over $(y,b)$ and using $\sum_b \pi(b \mid x_t) = 1$ and $\sum_b \mu(b \mid x_t) c_t(b,h_t) = \mathbb{E}[c_t \mid h_t]$,

$$\sum_{y,b} w_{y,b} = \sum_{t \ge 1} \gamma^t\, \mathbb{E}\Bigl[\prod_{i=1}^{t-1} c_i\Bigr] - \sum_{t \ge 1} \gamma^t\, \mathbb{E}\Bigl[\prod_{i=1}^{t} c_i\Bigr] = \gamma C - (C - 1) = 1 - (1-\gamma) C,$$

all series being absolutely convergent since $C \le 1/(1-\gamma)$. The bounds $1 \le C \le 1/(1-\gamma)$ give $0 \le \eta \le \gamma$, and the triangle inequality gives the estimate.

## Sources

- R. Munos, T. Stepleton, A. Harutyunyan, M. G. Bellemare, *Safe and Efficient Off-Policy Reinforcement Learning*, Advances in Neural Information Processing Systems 29 (NIPS 2016), arXiv:1606.02647v2, <https://arxiv.org/abs/1606.02647v2>: Section 3.1, Remark 1 and the proof of Theorem 1 (the weights $w_{y,b}$ and their sum $\gamma C - (C-1)$).
