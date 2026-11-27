# Upper confidence bound value iteration (UCBVI)

UCBVI is an optimistic model-based algorithm for stationary episodic MDPs. Before each episode it runs backward value iteration on the empirical transition model with an exploration bonus added to every Q-value, clipped at $H$, and then follows the greedy policy of the resulting optimistic Q-values for the whole episode.

The setting is the [online episodic protocol](online-episodic-learning-and-regret.md) for a stationary [episodic MDP](episodic-mdp-with-stage-dependent-transitions.md): one unknown transition distribution $P(\cdot \mid x, a)$ serves every stage, the deterministic reward $R(x, a) \in [0, 1]$ is known, and $S$, $A$, $H$ and the number of steps $T = KH$ are known. Let $\delta \in (0, 1)$ and $L = \ln(5SAT/\delta)$.

Before episode $k$, from all transitions $(x, a, y)$ observed in episodes $1, \dots, k-1$ at any stage, UCBVI forms the counts $N_k(x, a, y)$ and $N_k(x, a) = \sum_y N_k(x, a, y)$, the stage-wise state counts $N'_{k,h}(y)$ (visits to $y$ at stage $h$), and $\hat P_k(y \mid x, a) = N_k(x, a, y)/N_k(x, a)$ for pairs with $N_k(x, a) > 0$. It sets $V_{k,H+1} \equiv 0$ and, for $h = H, H-1, \dots, 1$ and every pair $(x, a)$,

$$
Q_{k,h}(x, a) = \min\Big\{Q_{k-1,h}(x, a),\ H,\ R(x, a) + \sum_{y} \hat P_k(y \mid x, a)\, V_{k,h+1}(y) + b_{k,h}(x, a)\Big\} \quad \text{if } N_k(x, a) > 0,
$$

with $Q_{0,h} \equiv H$ before the first episode, $Q_{k,h}(x, a) = H$ for unvisited pairs and $V_{k,h}(x) = \max_a Q_{k,h}(x, a)$. In episode $k$ it plays $a_{k,h} \in \arg\max_a Q_{k,h}(x_{k,h}, a)$. Two bonuses give two variants.

- UCBVI-CH (Chernoff–Hoeffding): $b_{k,h}(x, a) = 7HL / \sqrt{N_k(x, a)}$.
- UCBVI-BF (Bernstein–Freedman): with $\mathrm{Var}_k$ the variance under $Y \sim \hat P_k(\cdot \mid x, a)$,

$$
b_{k,h}(x, a) = \sqrt{\frac{8L\, \mathrm{Var}_k\big(V_{k,h+1}(Y)\big)}{N_k(x, a)}} + \frac{14HL}{3N_k(x, a)} + \sqrt{\frac{8 \sum_y \hat P_k(y \mid x, a) \min\big\{100^2 H^3 S^2 A L^2 / N'_{k,h+1}(y),\ H^2\big\}}{N_k(x, a)}},
$$

where the minimum is $H^2$ when $N'_{k,h+1}(y) = 0$.

## Depends on

- [Episodic Markov decision process with stage-dependent transitions](episodic-mdp-with-stage-dependent-transitions.md)
- [Online episodic learning and regret](online-episodic-learning-and-regret.md)

## Proof depends on

None.

## Expansion

The bonus is added to the Q-values directly rather than through a confidence set of transition models, as in UCRL2. The analysis concentrates $(\hat P_k - P) V_{h+1}^\star$, a one-dimensional quantity because $V^\star$ is fixed, and treats the correction $(\hat P_k - P)(V_{k,h+1} - V_{h+1}^\star)$ separately; this is what improves the dependence on $S$ from $S$ to $\sqrt{S}$. The empirical-variance bonus of UCBVI-BF tracks the variance of $V^\star$ at the next state, and its last term keeps the estimates optimistic while the empirical variance of $V_{k,h+1}$ may still underestimate that of $V^\star$.

Since the counts pool all stages, the algorithm and its guarantees use $P_1 = \dots = P_H$. Applied to a stage-dependent MDP by treating $(x, h)$ as a state, it runs with $SH$ states. The theorems state the logarithmic factor as $\ln(5HSAT/\delta)$ while the displayed bonuses use $\ln(5SAT/\delta)$. Each episode costs one optimistic value iteration, of the same order as solving a known MDP.

## Sources

- M. G. Azar, I. Osband and R. Munos, "Minimax Regret Bounds for Reinforcement Learning", *Proceedings of the 34th International Conference on Machine Learning* (ICML 2017), PMLR 70, Section 3, Algorithms 1 to 4 (UCBVI, UCB-Q-values, bonus_1, bonus_2) and Assumption 1; the same numbering in arXiv:1703.05449v2, whose appendix table of notation defines $N'_{k,h}$. [PDF](https://proceedings.mlr.press/v70/azar17a/azar17a.pdf)
