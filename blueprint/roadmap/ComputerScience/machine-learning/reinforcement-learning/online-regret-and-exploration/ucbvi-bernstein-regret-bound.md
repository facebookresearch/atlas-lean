# Regret bound for UCBVI with Bernstein bonuses

In a stationary episodic MDP with known rewards in $[0,1]$, UCBVI with the empirical-Bernstein bonus has regret at most $30HL\sqrt{SAK} + 2500H^2S^2AL^2 + 4H^{3/2}\sqrt{KL}$ after $K$ episodes, with probability at least $1-\delta$, where $L = \ln(5HSAT/\delta)$. For $T = KH \ge H^3S^3A$ and $SA \ge H$ this is $\tilde O(\sqrt{HSAT})$.

Let $M$ be a stationary [episodic MDP](episodic-mdp-with-stage-dependent-transitions.md) with $S$ states, $A$ actions, horizon $H$, one transition distribution $P$ for all stages and a known deterministic reward $R(x, a) \in [0, 1]$, and let the initial states $x_{k,1}$ be arbitrary. Run [UCBVI](upper-confidence-bound-value-iteration.md) with the Bernstein–Freedman bonus (UCBVI-BF) for $K$ episodes. Then for every $\delta \in (0, 1)$, with probability at least $1 - \delta$,

$$
\mathrm{Regret}(K) \le 30\, H L \sqrt{SAK} + 2500\, H^2 S^2 A L^2 + 4\, H^{3/2} \sqrt{KL}, \qquad L = \ln(5HSAT/\delta),\ T = KH,
$$

where the algorithm's bonus uses $L' = \ln(5SAT/\delta)$ as the algorithm displays it, and where $\mathrm{Regret}(K)$ is the [episodic regret](online-episodic-learning-and-regret.md).

## Depends on

- [Upper confidence bound value iteration (UCBVI)](upper-confidence-bound-value-iteration.md)
- [Online episodic learning and regret](online-episodic-learning-and-regret.md)

## Proof depends on

- [Law of total variance for episodic returns](law-of-total-variance-for-episodic-returns.md)
- [Freedman's maximal inequality for adaptive supermartingales](../../../../Probability/concentration-inequalities/adaptive-martingale-tail-bounds/freedman-maximal-inequality.md)
- [Azuma-Hoeffding inequality for adaptive processes with bounded conditional ranges](../../../../Probability/concentration-inequalities/adaptive-martingale-tail-bounds/azuma-hoeffding-bounded-conditional-ranges.md)

## Expansion

In steps, $HL\sqrt{SAK} = L\sqrt{HSAT}$. Azar, Osband and Munos note that for $T \ge H^3S^3A$ and $SA \ge H$ the bound is $\tilde O(\sqrt{HSAT})$, which matches, up to logarithmic factors, the lower bound of order $\sqrt{HSAT}$ that they quote for stationary transitions from Osband and Van Roy; they note that the lower bound of Jaksch, Ortner and Auer is for weakly communicating MDPs and does not apply directly to the finite-horizon setting. Below that range the term of order $H^2S^2A$ dominates; removing such burn-in terms is the subject of [minimax regret without burn-in](minimax-regret-without-burn-in.md), stated for stage-dependent transitions. With stage-dependent transitions the reduction to $SH$ states gives a leading term of order $H\sqrt{SAT}$, consistent with the [stage-dependent lower bound](episodic-minimax-regret-lower-bound.md).

The proof follows that of the Hoeffding version, with three changes. The estimation errors $(\hat P_k - P)V_{h+1}^\star$ are bounded by Bernstein's inequality in terms of the next-state variance of $V^\star$. The bonuses, built from empirical variances, are related to the variances of $V^{\pi_k}$ along the played trajectories. The sum of those variances over all $K$ episodes is at most $TH$ plus lower-order terms, by the law of total variance per episode and Freedman's inequality across episodes, instead of the $TH^2$ a range bound would give. Solving the resulting inequality $U \lesssim L\sqrt{(TH + H^2U)SA}$ for the optimistic regret $U$ gives the bound.

The high-probability event of the full proof combines Bernstein's inequality for $(\hat P_k - P)V^\star$ and for each next-state frequency, Azuma's and Freedman's inequalities, and two tools that no page of the graph states. One is the empirical Bernstein inequality of Maurer and Pontil (Theorem 4 of their paper): for i.i.d. $Z_1, \dots, Z_n \in [0, 1]$ with $n \ge 2$ and sample variance $V_n$, with probability at least $1 - \delta$, $\mathbb{E}Z - \frac1n\sum_i Z_i \le \sqrt{2V_n\ln(2/\delta)/n} + 7\ln(2/\delta)/(3(n-1))$; it is what relates the empirical-variance bonus to the true variance of $V^\star$. The other is the $\ell_1$ deviation inequality for empirical distributions of Weissman, Ordentlich, Seroussi, Verdú and Weinberger, used for $\lVert \hat P_k(\cdot \mid x, a) - P(\cdot \mid x, a)\rVert_1$. Both are missing proof prerequisites of this theorem. A good expansion also gives pages to the steps of the appendix of arXiv:1703.05449v2: Lemma 1 (the high-probability event, which these inequalities make up), the variance inequality Lemma 2, the per-episode bound Lemma 3, the intermediate bounds of Lemmas 4 to 13, 16 and 17, the regret bound Lemma 14 and the optimism Lemma 19, from which Section C.2 concludes Theorem 2.

## Sources

- M. G. Azar, I. Osband and R. Munos, "Minimax Regret Bounds for Reinforcement Learning", *Proceedings of the 34th International Conference on Machine Learning* (ICML 2017), PMLR 70, Theorem 2 (regret bound for UCBVI-BF) and the remark after it, Assumption 1, Section 5.2 (proof sketch, steps on the sums of variances), the footnote on the lower bound in Section 1; the same theorem numbering in arXiv:1703.05449v2, whose appendix gives the full proof. [PDF](https://proceedings.mlr.press/v70/azar17a/azar17a.pdf)
- A. Maurer and M. Pontil, "Empirical Bernstein Bounds and Sample Variance Penalization", *Proceedings of the 22nd Annual Conference on Learning Theory* (COLT 2009), Theorem 4 in arXiv:0907.3740v1 (the empirical Bernstein inequality cited by Azar, Osband and Munos). [arXiv](https://arxiv.org/abs/0907.3740v1)
- T. Weissman, E. Ordentlich, G. Seroussi, S. Verdú and M. J. Weinberger, "Inequalities for the L1 Deviation of the Empirical Distribution", Technical Report HPL-2003-97 (R.1), HP Laboratories Palo Alto, 2003, Theorem 2.1, inequality (8), with Proposition 4.3 ($\varphi(\pi_P) \ge 2$). [PDF](https://web.archive.org/web/20220123001144/https://www.hpl.hp.com/techreports/2003/HPL-2003-97R1.pdf)
- C. Jin, Z. Allen-Zhu, S. Bubeck and M. I. Jordan, "Is Q-learning Provably Efficient?", NeurIPS 2018, Table 1 and footnote 2 (UCBVI at $\tilde O(\sqrt{H^2SAT})$ for stage-dependent transitions). [PDF](https://proceedings.neurips.cc/paper_files/paper/2018/file/d3b1fb02964aa64e257f9f26a31f72cf-Paper.pdf)
