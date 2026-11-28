# Minimax-optimal episodic regret without burn-in

For episodic MDPs with stage-dependent transitions and total reward per episode in $[0, H]$, for each number of episodes $K \ge 1$, a modified Monotonic Value Propagation algorithm run with $K$ and $\delta$ as inputs has regret of order $\min\{\sqrt{SAH^3K\log^5(SAHK/\delta)},\ HK\}$ with probability at least $1-\delta$. This matches the minimax lower bound up to logarithmic factors with no minimum sample size.

There is a universal constant $C$ such that the following holds. Fix integers $S, A, H, K \ge 1$ and $\delta \in (0, 1)$, and let $\mathfrak{A}$ be the modified Monotonic Value Propagation algorithm described below, whose only inputs are the state set, the action set, the horizon $H$, the number of episodes $K$ and $\delta$. Let $M$ be any [episodic MDP](episodic-mdp-with-stage-dependent-transitions.md) with $S$ states, $A$ actions, horizon $H$, stage-dependent transition kernels $P_h$, and random immediate rewards $r_h' \ge 0$ with distributions $R_{s,a,h}$: given the history and the current triple $(s_h, a_h, h) = (s, a, h)$, the pair $(r_h', s_{h+1})$ has the product law $R_{s,a,h} \otimes P_h(\cdot \mid s, a)$, so the reward and the next state are independent of each other and of earlier outcomes. Every trajectory has total reward $\sum_{h=1}^H r_h' \in [0, H]$. In each of the $K$ episodes the initial state is drawn independently from a fixed distribution $\mu$, and $\mathfrak{A}$ learns about $M$ only from the states, actions and rewards it observes. For a deterministic Markov policy $\pi$, the value under these random rewards is $V_h^\pi(s) = \mathbb{E}_\pi\big[\sum_{j=h}^H r_j' \mid s_h = s\big]$, the expectation over the rewards and the transitions, and $V_h^\star(s) = \max_\pi V_h^\pi(s)$; the regret is the [episodic regret](online-episodic-learning-and-regret.md) for these values, $\mathrm{Regret}(K) = \sum_{k=1}^K (V_1^\star(s_1^k) - V_1^{\pi^k}(s_1^k))$, where $\pi^k$ is the policy $\mathfrak{A}$ plays in episode $k$. Then with probability at least $1 - \delta$

$$
\mathrm{Regret}(K) \le C \min\Big\{\sqrt{SAH^3K \log^5\frac{SAHK}{\delta}},\ HK\Big\}.
$$

These values agree with those of the MDP whose deterministic reward is the mean reward $r_h(s, a) = \mathbb{E}[r_h'] \in [0, H]$; the linked model page normalizes rewards per step to $[0, 1]$ instead, which this total-reward assumption includes as a special case.

## Depends on

- [Online episodic learning and regret](online-episodic-learning-and-regret.md)
- [Episodic Markov decision process with stage-dependent transitions](episodic-mdp-with-stage-dependent-transitions.md)

## Proof depends on

- [Freedman's maximal inequality for adaptive supermartingales](../../../../Probability/concentration-inequalities/adaptive-martingale-tail-bounds/freedman-maximal-inequality.md)

## Expansion

The algorithm is optimistic and model-based, like [UCBVI](upper-confidence-bound-value-iteration.md), with three changes. It works in epochs: whenever the visit count of some triple $(s, a, h)$ reaches a power of $2$, it rebuilds the empirical transition kernel and mean reward of that triple from the samples of the current epoch only, about the second half of its samples, and recomputes $Q_h(s, a) = \min\{\hat r_h(s, a) + \langle \hat P_{s,a,h}, V_{h+1}\rangle + b_h(s, a),\ H\}$ backward over $h$. Its bonus is the monotonic Bernstein-type bonus of Zhang, Ji and Du, built from the empirical variance of $V_{h+1}$ under $\hat P_{s,a,h}$, the empirical variance of the rewards and a term $H\log(1/\delta')/N_h(s,a)$. The policy is greedy for the current optimistic $Q$.

The bound is in episodes; it gives a sample complexity of $\tilde O(SAH^3/\varepsilon^2)$ episodes, that is $\tilde O(SAH^4/\varepsilon^2)$ transitions, for every $\varepsilon \in (0, H]$. The lower bound that it matches is of order $\min\{\sqrt{SAH^3K}, HK\}$, which Zhang, Chen, Lee and Du attribute to Jin, Allen-Zhu, Bubeck and Jordan and to Domingues, Ménard, Kaufmann and Valko; for per-step rewards in $[0, 1]$ the [stage-dependent lower bound](episodic-minimax-regret-lower-bound.md) gives its $\sqrt{SAH^3K}$ branch for $K \ge HSA$, under that theorem's conditions on $S$, $A$ and $H$. Earlier asymptotically optimal bounds, such as the one for UCBVI, reach the order $\sqrt{SAH^3K}$ only after a burn-in, a minimum number of episodes polynomial in $S$, $A$ and $H$: the paper notes that no earlier bound was optimal for $SAH \le K \lesssim \min\{SAH^5, S^3AH\}$. The total-reward normalization of the theorem is weaker than per-step rewards in $[0,1]$, so the theorem applies to that case as well.

The key step of the proof decouples the statistical dependence between the empirical kernel $\hat P_{s,a,h}$ and the value estimate $V_{h+1}$ it is applied to: because each kernel changes only $O(\log K)$ times, a covering argument over the possible value iterates, combined with Freedman's inequality, bounds $\langle \hat P_{s,a,h} - P_{s,a,h}, V_{h+1}\rangle$ without paying for the $S$-dimensional model.

A good expansion adds pages for the results that the proof of Theorem 1 (Sections 4 and 5 and Appendices A to C of arXiv:2307.13586v4) uses and that the graph does not state:

- Freedman's inequality in the form of Lemma 15, for martingales with increments bounded by $c$ and with the predictable quadratic variation inside the bound. The graph's Freedman page is stated for processes with discrete steps, which covers the transition terms but not the reward terms, whose distributions on $[0, H]$ are arbitrary.
- Lemma 16, $\mathrm{Var}(X^2) \le 4C^2\mathrm{Var}(X)$ for a random variable $X$ with $\lvert X\rvert \le C$ almost surely, since $\mathrm{Var}(X^2) \le \mathbb{E}[(X - \mathbb{E}X)^2(X + \mathbb{E}X)^2]$. The source words the hypothesis as "$C_{\max}$ is the largest possible value of $X$", which must be read as a bound on $\lvert X\rvert$: for $X$ uniform on $\{-1, 0\}$ the largest value is $0$ while $\mathrm{Var}(X^2) = 1/4$. Its applications satisfy the bound on $\lvert X\rvert$, with $X$ in $[-H, H]$ in the bound on $T_8$ before (78) and in $[0, H]$ in the proof of Lemma 7 (Appendix B.3).
- Lemma 19, the empirical Bernstein inequality of Maurer and Pontil, used in the proof of the optimism Lemma 8 and in Lemma 21.
- Lemma 20, the bound $2SAH\log_2 K$ on the sum of the inverse visit counts under the doubling rule.
- The steps specific to the algorithm: the counting Lemma 5 and the uniform concentration Lemmas 6 and 7 behind the decoupling, optimism (Lemma 8), the regret decomposition (Lemma 9), the bounds of Lemmas 10 and 11 on the terms of that decomposition, and the reward-estimation Lemma 21.

Lemma 17 of the source, which compares sums of bounded variables with the sums of their conditional means, is not used for Theorem 1: it enters only the proofs of Theorems 2 to 4 and of the lower bounds (Appendices D to G).

## Sources

- Z. Zhang, Y. Chen, J. D. Lee and S. S. Du, "Settling the Sample Complexity of Online Reinforcement Learning", arXiv:2307.13586v4, the version accepted to the Journal of the ACM: Theorem 1 and the bound (8), the minimax lower bound (1), Section 1.1 (burn-in costs of prior bounds), Section 2 with Assumption 1 and the regret (17), Section 3 with Algorithm 1 and the bonus (19), Section 4 (decoupling and the doubling rule), and the statement of Freedman's inequality among the preliminary facts. Extended abstract in *Proceedings of the 37th Annual Conference on Learning Theory* (COLT 2024), PMLR 247, which refers to arXiv version 3 for the full paper; journal version in *Journal of the ACM* (2025), doi:10.1145/3733592. [arXiv](https://arxiv.org/abs/2307.13586v4)
