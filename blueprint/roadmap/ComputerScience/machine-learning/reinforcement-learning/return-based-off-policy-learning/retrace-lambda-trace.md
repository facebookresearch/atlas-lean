# Retrace(λ) trace

The Retrace(λ) trace is defined by $c_s = \lambda \min\bigl(1, \pi(a_s \mid x_s)/\mu(a_s \mid x_s)\bigr)$ wherever $\mu(a_s \mid x_s) > 0$, with $0 \le \lambda \le 1$: an importance ratio truncated at $1$ and scaled by $\lambda$. It is a Markovian trace, admissible for every target $\pi$ and behaviour $\mu$.

Let $M$ be a Markov decision process with a finite nonempty set of states $X$ and a finite nonempty set of actions $A$, let $\pi$ (target) and $\mu$ (behaviour) be stochastic policies and let $\lambda \in [0,1]$. The Retrace(λ) trace is the Markovian trace given by

$$c(b, y) = \begin{cases} \lambda \min\Bigl(1, \dfrac{\pi(b \mid y)}{\mu(b \mid y)}\Bigr) & \text{if } \mu(b \mid y) > 0, \\ \lambda & \text{if } \mu(b \mid y) = 0, \end{cases}$$

the second line being a convention for actions the behaviour never draws (any value in $[0,\infty)$ would serve). It satisfies $0 \le c \le \lambda \le 1$ and, for every state $y$ and action $b$,

$$\mu(b \mid y)\, c(b,y) = \lambda \min\bigl(\mu(b \mid y), \pi(b \mid y)\bigr) \le \pi(b \mid y),$$

so it is admissible for $(\pi, \mu)$. If $\pi(\cdot \mid y)$ is the point mass at an action $g(y)$, then $c(b, y) = \lambda\, \mathbf{1}\{b = g(y)\}$ for every action $b$ with $\mu(b \mid y) > 0$: the trace is cut at the first action that differs from $g$.

Other traces of the same form, for comparison: importance sampling, $c = \pi/\mu$ on actions with $\mu > 0$, is admissible, with equality $\mu c = \pi$ on those actions, and makes the return-based operator return $Q^\pi$ for every $Q$ when every $\pi(\cdot \mid y)$ charges only actions with $\mu(\cdot \mid y) > 0$ (the source states this without the support condition); the off-policy $Q^\pi(\lambda)$ trace $c = \lambda$ is admissible only when $\lambda \mu \le \pi$; and tree-backup, $c = \lambda \pi(a_s \mid x_s)$, is admissible since $\lambda \mu \pi \le \pi$. Because $\min(1, \pi/\mu) \ge \pi$, Retrace(λ) cuts traces no more than tree-backup with the same $\lambda$.

## Depends on

- [Causal trace](causal-trace.md)
- [Stochastic policy](../stochastic-policies-and-discounted-occupancy/stochastic-policy.md)
- [Return-based off-policy operator](return-based-off-policy-operator.md)
- [Action value of a stochastic policy](../performance-difference-lemma/stoch-qvalue.md)

## Proof depends on

- [Causal trace](causal-trace.md)
- [Return-based off-policy operator](return-based-off-policy-operator.md)
- [Action value of a stochastic policy](../performance-difference-lemma/stoch-qvalue.md)
- [State-action contraction coefficient of a return-based operator](state-action-contraction-coefficient.md)

## Expansion

A definition; the listed properties are direct. If $\mu(b \mid y) > 0$ then $\mu \cdot \lambda \min(1, \pi/\mu) = \lambda \min(\mu, \pi)$, and if $\mu(b \mid y) = 0$ both sides vanish. For a point-mass target and $\mu(b \mid y) > 0$, $\min(1, 1/\mu(g(y) \mid y)) = 1$ and $\min(1, 0) = 0$. For the comparison, $\min(1, \pi/\mu) \ge \pi$ holds since $\pi \le 1$ and $\pi/\mu \ge \pi$. The importance-sampling claim follows from the weights of the state-action contraction coefficient: for that trace the factor $\pi(b \mid x_t) - \mu(b \mid x_t)\, c_t(b, h_t)$ inside each weight equals $\pi(b \mid x_t)\mathbf{1}\{\mu(b \mid x_t) = 0\}$, while the trace product, the indicator, the expectation and the sum over time remain; under the support condition the factor vanishes at every state the trajectory reaches, so every weight is zero and $\mathcal{R}Q = Q^\pi$.

## Sources

- R. Munos, T. Stepleton, A. Harutyunyan, M. G. Bellemare, *Safe and Efficient Off-Policy Reinforcement Learning*, Advances in Neural Information Processing Systems 29 (NIPS 2016), arXiv:1606.02647v2, <https://arxiv.org/abs/1606.02647v2>: Section 2 (the paragraphs on importance sampling, $Q^\pi(\lambda)$, tree-backup and Retrace(λ)) and Table 1; Section 3.3 (the rewriting $\mu c = \lambda \min(\pi, \mu)$).
