# Regret bound for Q-learning with Bernstein bonuses

In an episodic MDP with stage-dependent transitions, rewards in $[0,1]$ and adversarial initial states, optimistic Q-learning with an empirical-Bernstein bonus has regret $O(\sqrt{H^3SAT\iota} + \sqrt{H^9S^3A^3}\,\iota^2)$ with probability at least $1-p$, where $T = KH$ and $\iota = \log(SAT/p)$: a factor $\sqrt{H}$ better than the Hoeffding bonus in the leading term.

There are absolute constants $c_1, c_2 > 0$ such that the following holds, with an absolute constant in the $O(\cdot)$ below. Let $p \in (0, 1)$ and let $M$ be any [episodic MDP](episodic-mdp-with-stage-dependent-transitions.md) with $S$ states, $A$ actions, horizon $H$, stage-dependent transition kernels and deterministic rewards $r_h \in [0, 1]$, played for $K$ episodes in the [online episodic protocol](online-episodic-learning-and-regret.md) with initial states chosen by an adversary, and let $T = KH$. Then [Q-learning with the UCB-Bernstein bonus](optimistic-q-learning-with-ucb-bonuses.md) built from $\beta_t$ with these constants and $\iota = \log(SAT/p)$, which uses only $S$, $A$, $H$, $T$ and $p$ and the observed transitions and rewards, satisfies with probability at least $1 - p$

$$
\mathrm{Regret}(K) \le O\big(\sqrt{H^3 S A T \iota} + \sqrt{H^9 S^3 A^3}\, \iota^2\big).
$$

## Depends on

- [Q-learning with upper-confidence exploration bonuses](optimistic-q-learning-with-ucb-bonuses.md)
- [Online episodic learning and regret](online-episodic-learning-and-regret.md)

## Proof depends on

- [Learning-rate weights of optimistic Q-learning](learning-rate-weights-of-optimistic-q-learning.md)
- [Law of total variance for episodic returns](law-of-total-variance-for-episodic-returns.md)
- [Freedman's maximal inequality for adaptive supermartingales](../../../../Probability/concentration-inequalities/adaptive-martingale-tail-bounds/freedman-maximal-inequality.md)
- [Azuma-Hoeffding inequality for adaptive processes with bounded conditional ranges](../../../../Probability/concentration-inequalities/adaptive-martingale-tail-bounds/azuma-hoeffding-bounded-conditional-ranges.md)

## Expansion

The additive term $\sqrt{H^9S^3A^3}\,\iota^2$ dominates until $T$ is large compared with $S$, $A$ and $H$; Jin, Allen-Zhu, Bubeck and Jordan leave open whether it is necessary. The leading term $\sqrt{H^3SAT}$, which is $\sqrt{H^4SAK}$ in episodes, is a factor $\sqrt{H}$ above the [stage-dependent lower bound](episodic-minimax-regret-lower-bound.md).

The proof keeps the recursion of the Hoeffding case. A coarse bound, valid because $\beta_t \le c_2\sqrt{H^3\iota/t}$, controls $Q^k - Q^\star$ without optimism. A finer bound replaces the range $H$ in the concentration of $\sum_i \alpha_t^i ((\hat P_h^{k_i} - P_h)V_{h+1}^\star)$ by the empirical variance $W_t$, using a martingale Bernstein inequality, which the source calls the Azuma–Bernstein inequality and which is a form of Freedman's inequality, and the gap between $W_t$ and the true next-state variance of $V^\star$; this gives optimism for the Bernstein bonus. The sum of the bonuses is then controlled by the sum of next-state variances of $V^{\pi_k}$ along the played trajectories, which the law of total variance and a martingale argument bound by $c(HT + H^3\iota)$ with probability at least $1 - p$ (Lemma C.5 of the full version), instead of the $H^2 T$ a range bound gives.

## Sources

- C. Jin, Z. Allen-Zhu, S. Bubeck and M. I. Jordan, "Is Q-learning Provably Efficient?", *Advances in Neural Information Processing Systems 31* (NeurIPS 2018), Theorem 3 (Bernstein) and the discussion after it. [PDF](https://proceedings.neurips.cc/paper_files/paper/2018/file/d3b1fb02964aa64e257f9f26a31f72cf-Paper.pdf)
- C. Jin, Z. Allen-Zhu, S. Bubeck and M. I. Jordan, "Is Q-learning Provably Efficient?", full version arXiv:1807.03765v1, Appendix C: the restated Theorem 2 with absolute constants $c_1, c_2$ (the NeurIPS Theorem 3), the definitions (C.2) and (C.3), Algorithm 2 and Lemmas C.1 to C.7. [arXiv](https://arxiv.org/abs/1807.03765v1)
