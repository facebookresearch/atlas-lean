# Admissible trace products have mean at most one

For a causal trace admissible for $(\pi, \mu)$, the expected trace product $\mathbb{E}^\mu_{x,a}\bigl[\prod_{s=1}^t c_s\bigr]$ is at most $1$ for every $t$, so the expected discounted trace mass lies in $[1, 1/(1-\gamma)]$ and the return-based operator is defined.

Let $M$ be a Markov decision process with a finite set of states $X$, a finite nonempty set of actions $A$ and transition probabilities $P(x' \mid x,a)$ that are nonnegative and sum to $1$ over $x'$, and let $0 \le \gamma < 1$. Let $\pi, \mu$ be stochastic policies and $c$ a causal trace admissible for $(\pi, \mu)$. Then for every pair $(x,a)$ and every $t \ge 1$,

$$\mathbb{E}^\mu_{x,a}[c_t \mid h_t] = \sum_{b \in A} \mu(b \mid x_t)\, c_t(b, h_t) \le 1, \qquad \mathbb{E}^\mu_{x,a}\Bigl[\prod_{s=1}^t c_s\Bigr] \le 1,$$

and consequently the expected discounted trace mass satisfies $1 \le C(x,a) \le 1/(1-\gamma)$.

## Depends on

- [Causal trace](causal-trace.md)
- [Return-based off-policy operator](return-based-off-policy-operator.md)

## Proof depends on

- [History-dependent randomized policies and trajectory laws](../../../heuristic-search-and-planning/markov-decision-processes/history-dependent-randomized-policies-and-trajectory-laws.md)
- [Causal trace](causal-trace.md)
- [Return-based off-policy operator](return-based-off-policy-operator.md)

## Expansion

Given the history $h_t$, the action $a_t$ has law $\mu(\cdot \mid x_t)$, which gives the first identity; admissibility bounds it by $\sum_b \pi(b \mid x_t) = 1$. The product $\prod_{s<t} c_s$ is a function of $h_t$, so the tower property gives $\mathbb{E}[\prod_{s \le t} c_s] = \mathbb{E}[\prod_{s<t} c_s\, \mathbb{E}[c_t \mid h_t]] \le \mathbb{E}[\prod_{s<t} c_s]$, and induction from the empty product gives the bound. Summing $\gamma^t$ times these bounds gives $C \le \sum_t \gamma^t$; $C \ge 1$ comes from the $t = 0$ term.

## Sources

- R. Munos, T. Stepleton, A. Harutyunyan, M. G. Bellemare, *Safe and Efficient Off-Policy Reinforcement Learning*, Advances in Neural Information Processing Systems 29 (NIPS 2016), arXiv:1606.02647v2, <https://arxiv.org/abs/1606.02647v2>: Section 3.1 (the step averaging $c_t$ over $a_t$ given $\mathcal{F}_t$ in the proof of Theorem 1, and $C \ge 1$) and Remark 1 ($\eta(x,a) \in [0, \gamma]$, which uses $C \le 1/(1-\gamma)$).
