# Regret bound for UCBVI with Hoeffding bonuses

In a stationary episodic MDP with known rewards in $[0,1]$, UCBVI with the Hoeffding bonus has regret at most $20H^{3/2}L\sqrt{SAK} + 250H^2S^2AL^2$ after $K$ episodes, with probability at least $1-\delta$, where $L = \ln(5HSAT/\delta)$ and $T = KH$. For large $T$ this is $\tilde O(H\sqrt{SAT})$.

Let $M$ be a stationary [episodic MDP](episodic-mdp-with-stage-dependent-transitions.md) with $S$ states, $A$ actions, horizon $H$, one transition distribution $P$ for all stages and a known deterministic reward $R(x, a) \in [0, 1]$, and let the initial states $x_{k,1}$ be arbitrary. Run [UCBVI](upper-confidence-bound-value-iteration.md) with the Hoeffding bonus (UCBVI-CH), $b_{k,h}(x, a) = 7HL'/\sqrt{N_k(x, a)}$ with $L' = \ln(5SAT/\delta)$ as the algorithm displays it, for $K$ episodes. Then for every $\delta \in (0, 1)$, with probability at least $1 - \delta$,

$$
\mathrm{Regret}(K) \le 20\, H^{3/2} L \sqrt{SAK} + 250\, H^2 S^2 A L^2, \qquad L = \ln(5HSAT/\delta),\ T = KH,
$$

where $\mathrm{Regret}(K)$ is the [episodic regret](online-episodic-learning-and-regret.md).

## Depends on

- [Upper confidence bound value iteration (UCBVI)](upper-confidence-bound-value-iteration.md)
- [Online episodic learning and regret](online-episodic-learning-and-regret.md)

## Proof depends on

- [Azuma-Hoeffding inequality for adaptive processes with bounded conditional ranges](../../../../Probability/concentration-inequalities/adaptive-martingale-tail-bounds/azuma-hoeffding-bounded-conditional-ranges.md)
- [Hoeffding's inequality for averages of bounded variables](../../../../Probability/concentration-inequalities/hoeffding-s-inequality/measure-real-avg-sub-ge-le.md)
- [Freedman's maximal inequality for adaptive supermartingales](../../../../Probability/concentration-inequalities/adaptive-martingale-tail-bounds/freedman-maximal-inequality.md)

## Expansion

In terms of steps, $H^{3/2}\sqrt{SAK} = H\sqrt{SAT}$. Azar, Osband and Munos note that for $T \ge HS^3A$ and $SA \ge H$ the bound is $\tilde O(H\sqrt{SAT})$: below that range the second term, of order $H^2S^2A$, is not dominated. The bound is for stationary transitions; with stage-dependent transitions the reduction to $SH$ states multiplies the leading term by $\sqrt{H}$.

The proof first shows, by backward induction on $h$ and Hoeffding's inequality for $(\hat P_k - P)V_{h+1}^\star$, that with high probability $V_{k,h} \ge V_h^\star$ for all $k$ and $h$, so the regret is at most $\sum_k (V_{k,1} - V_1^{\pi_k})(x_{k,1})$. With $\tilde\delta_{k,h} = (V_{k,h} - V_h^{\pi_k})(x_{k,h})$, the optimistic gap satisfies $\tilde\delta_{k,h} \le (\hat P_k - P)\Delta_{k,h+1}(x_{k,h}) + \tilde\delta_{k,h+1} + \epsilon_{k,h} + b_{k,h} + e_{k,h}$, where $\Delta_{k,h+1} = V_{h+1}^\star - V_{h+1}^{\pi_k}$, $e_{k,h} = (\hat P_k - P)V_{h+1}^\star(x_{k,h})$ is the estimation error and $\epsilon_{k,h}$ a martingale difference. Bernstein's inequality for each next-state frequency bounds the correction term by $\bar\epsilon_{k,h} + \frac1H\tilde\delta_{k,h+1}$ plus terms of order $SH^2L/n_{k,h}$, with $\bar\epsilon_{k,h}$ another martingale difference and $n_{k,h} = N_k(x_{k,h}, \pi_k(x_{k,h}))$. Hence $\tilde\delta_{k,h} \le (1 + \frac1H)\tilde\delta_{k,h+1} + \epsilon_{k,h} + \bar\epsilon_{k,h} + b_{k,h} + e_{k,h}$ up to those terms, which unrolls with $(1 + \frac1H)^H \le e$. The martingale terms are bounded by the Azuma–Hoeffding inequality by $O(H\sqrt{TL})$; the bonuses and, by Hoeffding's inequality, the estimation errors sum to $O(HL\sqrt{SAT})$ by the pigeonhole bound $\sum_{x,a}\sum_{n \le N_K(x,a)} n^{-1/2} \lesssim \sqrt{SAT}$; the neglected terms of order $SH^2L/n_{k,h}$ sum to the second-order term of order $S^2AH^2L^2$. Bernstein's inequality for sums of independent indicators is the deterministic-variance case of Freedman's inequality.

## Sources

- C. Jin, Z. Allen-Zhu, S. Bubeck and M. I. Jordan, "Is Q-learning Provably Efficient?", NeurIPS 2018, footnote 2 (the factor $\sqrt{H}$ for stage-dependent transitions). [PDF](https://proceedings.neurips.cc/paper_files/paper/2018/file/d3b1fb02964aa64e257f9f26a31f72cf-Paper.pdf)
- M. G. Azar, I. Osband and R. Munos, "Minimax Regret Bounds for Reinforcement Learning", *Proceedings of the 34th International Conference on Machine Learning* (ICML 2017), PMLR 70, Theorem 1 (regret bound for UCBVI-CH) and the remark after it, Assumption 1, Section 5.1 (proof sketch, Steps 1 to 4, including the use of Bernstein's inequality in Step 1); the same theorem numbering in arXiv:1703.05449v2, whose appendix carries out the full argument for the Bernstein variant. [PDF](https://proceedings.mlr.press/v70/azar17a/azar17a.pdf)
