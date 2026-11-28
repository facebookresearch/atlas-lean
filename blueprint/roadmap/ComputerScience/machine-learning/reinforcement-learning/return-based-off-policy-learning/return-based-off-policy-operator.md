# Return-based off-policy operator

Given a target policy $\pi$, a behaviour policy $\mu$ and a causal trace $c$, the return-based operator $\mathcal{R}$ is defined by correcting $Q(x,a)$ with trace-weighted temporal differences along behaviour trajectories that start with the pair $(x,a)$; it is defined whenever the expected discounted trace mass is finite.

Let $M$ be a Markov decision process with a finite set of states $X$, a finite nonempty set of actions $A$, real rewards $r(x,a)$ and transition probabilities $P(x' \mid x,a)$ that are nonnegative and sum to $1$ over $x'$, and let $0 \le \gamma < 1$. Let $\pi$ and $\mu$ be stochastic policies. For a pair $(x,a)$, let $\mathbb{P}^\mu_{x,a}$ denote the trajectory law, on histories of every length, of the history-dependent policy that takes the action $a$ at the initial state $x_0 = x$ and draws $a_t \sim \mu(\cdot \mid x_t)$ for $t \ge 1$; the initial action is forced even when $\mu(a \mid x) = 0$. Write $\mathbb{E}^\mu_{x,a}$ for its expectations, $r_t = r(x_t,a_t)$ and $(\mathbb{E}_\pi Q)(y) = \sum_b \pi(b \mid y) Q(y,b)$. For a causal trace $c$ the expected discounted trace mass at $(x,a)$ is

$$C(x,a) = \sum_{t \ge 0} \gamma^t\, \mathbb{E}^\mu_{x,a}\Bigl[\prod_{s=1}^t c_s\Bigr] \in [1, \infty] .$$

When $C(x,a) < \infty$ for every pair, the return-based operator sends a Q-function $Q$ to

$$\mathcal{R}Q(x,a) = Q(x,a) + \sum_{t \ge 0} \gamma^t\, \mathbb{E}^\mu_{x,a}\Bigl[\Bigl(\prod_{s=1}^t c_s\Bigr) \delta_t\Bigr], \qquad \delta_t = r_t + \gamma\, (\mathbb{E}_\pi Q)(x_{t+1}) - Q(x_t, a_t) .$$

The $t$-th expectation is a finite sum over histories of length $t+1$, and since $|\delta_t| \le \|r\| + (1+\gamma)\|Q\|$ the series is absolutely convergent. The source writes a single expectation of the whole series; here each time step contributes the expectation of a finite sum, and the definition is the absolutely convergent series of these numbers. The map $Q \mapsto \mathcal{R}Q$ is affine. With the Retrace(λ) trace it is the Retrace(λ) operator.

The source defines $\mathcal{R}$ for arbitrary nonnegative coefficients; without a bound on the trace mass the series can diverge (the constant trace $c_s = 2/\gamma$ gives $\gamma^t \prod_{s \le t} c_s = 2^t$), so the finiteness of $C$ is part of the definition here. Every admissible trace has $C \le 1/(1-\gamma)$, by [Admissible trace products have mean at most one](admissible-trace-products-mean-at-most-one.md).

## Depends on

- [History-dependent randomized policies and trajectory laws](../../../heuristic-search-and-planning/markov-decision-processes/history-dependent-randomized-policies-and-trajectory-laws.md)
- [Causal trace](causal-trace.md)
- [Stochastic policy](../stochastic-policies-and-discounted-occupancy/stochastic-policy.md)

## Proof depends on

- [History-dependent randomized policies and trajectory laws](../../../heuristic-search-and-planning/markov-decision-processes/history-dependent-randomized-policies-and-trajectory-laws.md)

## Expansion

A definition. The forced first action is a history-dependent randomized policy: the point mass at $a$ on the history $(x)$ and $\mu(\cdot \mid x_t)$ on longer histories. Under its law, for $t \ge 1$, $\mathbb{P}(a_t = b \mid h_t) = \mu(b \mid x_t)$, and for $t \ge 0$, $\mathbb{P}(x_{t+1} = y \mid h_t, a_t) = P(y \mid x_t, a_t)$, read off the product of policy and transition kernels. Absolute convergence: the $t$-th term is at most $\gamma^t (\|r\| + (1+\gamma)\|Q\|)\, \mathbb{E}[\prod_{s \le t} c_s]$, summable by $C < \infty$. $C \ge 1$ because the $t = 0$ term is $1$.

## Sources

- R. Munos, T. Stepleton, A. Harutyunyan, M. G. Bellemare, *Safe and Efficient Off-Policy Reinforcement Learning*, Advances in Neural Information Processing Systems 29 (NIPS 2016), arXiv:1606.02647v2, <https://arxiv.org/abs/1606.02647v2>: Section 1 (trajectories $x_0 = x, a_0 = a, r_0, x_1, a_1, \dots$ with $a_t \sim \mu(\cdot \mid x_t)$), Section 2, equation (3); Section 3.1, the constant $C$ in the proof of Theorem 1.
