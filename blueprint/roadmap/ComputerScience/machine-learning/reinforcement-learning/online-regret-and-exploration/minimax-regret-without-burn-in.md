# Minimax-optimal episodic regret without burn-in

For episodic MDPs with stage-dependent transitions and total reward per episode in $[0, H]$, a modified Monotonic Value Propagation algorithm has regret of order $\min\{\sqrt{SAH^3K\log^5(SAHK/\delta)},\ HK\}$ with probability at least $1-\delta$, for every number of episodes $K \ge 1$. This matches the minimax lower bound up to logarithmic factors with no minimum sample size.

Let $M$ be an [episodic MDP](episodic-mdp-with-stage-dependent-transitions.md) with $S$ states, $A$ actions, horizon $H$, stage-dependent transition kernels $P_h$, and random immediate rewards $r_h' \ge 0$ drawn from distributions $R_{s,a,h}$, such that every trajectory has total reward $\sum_{h=1}^H r_h' \in [0, H]$. In each of $K$ episodes the initial state is drawn independently from a fixed unknown distribution $\mu$, and the regret is the [episodic regret](online-episodic-learning-and-regret.md) $\mathrm{Regret}(K) = \sum_{k=1}^K (V_1^\star(s_1^k) - V_1^{\pi^k}(s_1^k))$. Then for every $K \ge 1$ and every $\delta \in (0, 1)$ there is an algorithm, the modified Monotonic Value Propagation described below, such that with probability at least $1 - \delta$

$$
\mathrm{Regret}(K) \le C \min\Big\{\sqrt{SAH^3K \log^5\frac{SAHK}{\delta}},\ HK\Big\}
$$

for a universal constant $C$.

## Depends on

- [Online episodic learning and regret](online-episodic-learning-and-regret.md)
- [Episodic Markov decision process with stage-dependent transitions](episodic-mdp-with-stage-dependent-transitions.md)

## Proof depends on

- [Freedman's maximal inequality for adaptive supermartingales](../../../../Probability/concentration-inequalities/adaptive-martingale-tail-bounds/freedman-maximal-inequality.md)

## Expansion

The algorithm is optimistic and model-based, like [UCBVI](upper-confidence-bound-value-iteration.md), with three changes. It works in epochs: whenever the visit count of some triple $(s, a, h)$ reaches a power of $2$, it rebuilds the empirical transition kernel and mean reward of that triple from the samples of the current epoch only, about the second half of its samples, and recomputes $Q_h(s, a) = \min\{\hat r_h(s, a) + \langle \hat P_{s,a,h}, V_{h+1}\rangle + b_h(s, a),\ H\}$ backward over $h$. Its bonus is the monotonic Bernstein-type bonus of Zhang, Ji and Du, built from the empirical variance of $V_{h+1}$ under $\hat P_{s,a,h}$, the empirical variance of the rewards and a term $H\log(1/\delta')/N_h(s,a)$. The policy is greedy for the current optimistic $Q$.

The bound is in episodes; it gives a sample complexity of $\tilde O(SAH^3/\varepsilon^2)$ episodes, that is $\tilde O(SAH^4/\varepsilon^2)$ transitions, for every $\varepsilon \in (0, H]$. The lower bound that it matches is of order $\min\{\sqrt{SAH^3K}, HK\}$, which Zhang, Chen, Lee and Du attribute to Jin, Allen-Zhu, Bubeck and Jordan and to Domingues, Ménard, Kaufmann and Valko; for per-step rewards in $[0, 1]$ the [stage-dependent lower bound](episodic-minimax-regret-lower-bound.md) gives its $\sqrt{SAH^3K}$ branch for $K \ge HSA$, under that theorem's conditions on $S$, $A$ and $H$. Earlier asymptotically optimal bounds, such as the one for UCBVI, reach the order $\sqrt{SAH^3K}$ only after a burn-in, a minimum number of episodes polynomial in $S$, $A$ and $H$: the paper notes that no earlier bound was optimal for $SAH \le K \lesssim \min\{SAH^5, S^3AH\}$. The total-reward normalization of the theorem is weaker than per-step rewards in $[0,1]$, so the theorem applies to that case as well.

The key step of the proof decouples the statistical dependence between the empirical kernel $\hat P_{s,a,h}$ and the value estimate $V_{h+1}$ it is applied to: because each kernel changes only $O(\log K)$ times, a covering argument over the possible value iterates, combined with Freedman's inequality, bounds $\langle \hat P_{s,a,h} - P_{s,a,h}, V_{h+1}\rangle$ without paying for the $S$-dimensional model. The graph's Freedman page is stated for processes with discrete steps, which covers the transition terms; the reward terms, with arbitrary reward distributions on $[0, H]$, need Freedman's inequality for general bounded martingale differences, which no page of the graph states, so that form is a missing proof prerequisite.

## Sources

- Z. Zhang, Y. Chen, J. D. Lee and S. S. Du, "Settling the Sample Complexity of Online Reinforcement Learning", arXiv:2307.13586v4, the version accepted to the Journal of the ACM: Theorem 1 and the bound (8), the minimax lower bound (1), Section 1.1 (burn-in costs of prior bounds), Section 2 with Assumption 1 and the regret (17), Section 3 with Algorithm 1 and the bonus (19), Section 4 (decoupling and the doubling rule), and the statement of Freedman's inequality among the preliminary facts. Extended abstract in *Proceedings of the 37th Annual Conference on Learning Theory* (COLT 2024), PMLR 247, which refers to arXiv version 3 for the full paper; journal version in *Journal of the ACM* (2025), doi:10.1145/3733592. [arXiv](https://arxiv.org/abs/2307.13586v4)
