# Regret bound for UCRL2

In a communicating MDP with $S$ states, $A$ actions, diameter $D$ and rewards in $[0,1]$, the regret of UCRL2 started in any state is at most $34DS\sqrt{AT\log(T/\delta)}$ after $T$ steps, simultaneously for all $T > 1$, with probability at least $1-\delta$. Only $S$ and $A$ are given to the algorithm.

Let $M$ be an unknown MDP with $S$ states, $A$ actions, rewards drawn independently from distributions on $[0, 1]$, and finite [diameter](diameter-of-an-mdp.md) $D = D(M)$, and run [UCRL2](ucrl2-and-extended-value-iteration.md) with confidence parameter $\delta \in (0, 1)$. Then for every initial state $s$, under the law of the run of UCRL2 started in $s$, with probability at least $1 - \delta$ the [regret against the optimal average reward](regret-against-optimal-average-reward.md) satisfies, simultaneously for every $T > 1$,

$$
\Delta(M, \mathrm{UCRL2}, s, T) \le 34 \cdot DS\sqrt{AT\log\frac{T}{\delta}} .
$$

## Depends on

- [UCRL2 and extended value iteration](ucrl2-and-extended-value-iteration.md)
- [Regret against the optimal average reward](regret-against-optimal-average-reward.md)

## Proof depends on

- [UCRL2 confidence sets contain the true MDP with high probability](ucrl2-confidence-sets-contain-true-mdp.md)
- [Finite-step optimal values have span at most the diameter](finite-step-value-span-at-most-diameter.md)
- [Azuma-Hoeffding inequality for adaptive processes with bounded conditional ranges](../../../../Probability/concentration-inequalities/adaptive-martingale-tail-bounds/azuma-hoeffding-bounded-conditional-ranges.md)
- [Hoeffding's inequality for averages of bounded variables](../../../../Probability/concentration-inequalities/hoeffding-s-inequality/measure-real-avg-sub-ge-le.md)

## Expansion

The bound is $\tilde O(DS\sqrt{AT})$ in the number $T$ of steps; the [lower bound for MDPs with a given diameter](regret-lower-bound-for-given-diameter.md) is of order $\sqrt{DSAT}$, so a gap of $\sqrt{DS}$ remains, which the authors conjecture is on the side of the upper bound. It implies that the average regret per step is at most $\varepsilon$ after $T \ge 4 \cdot 34^2 \cdot \frac{D^2S^2A}{\varepsilon^2}\log\frac{34DSA}{\delta\varepsilon}$ steps (Corollary 3). A gap-dependent version (Theorem 4), for UCRL2 run with $\delta = 1/(3T)$ and so depending on $T$, bounds the expected regret by $34^2 D^2S^2A\log(T)/g$ plus a term independent of $T$, with $g$ the gap in average reward between the best and second-best policy. An episodic MDP with stage-dependent transitions becomes an MDP with $SH$ states by augmenting the state with the stage; Jin, Allen-Zhu, Bubeck and Jordan note that this MDP is weakly communicating with diameter at least $H$, and the augmentation alone does not make the diameter finite. When it is finite, the bound is at least $\tilde O(\sqrt{H^4S^2AT})$ in steps, larger than the episodic bounds of [UCBVI](ucbvi-hoeffding-regret-bound.md) or [optimistic Q-learning](optimistic-q-learning-hoeffding-regret-bound.md).

The proof fixes the initial state, splits the regret into episodes, and takes the union bound over the horizons $T$ at the end (Section 4.4, (23)); no event across runs from different initial states is involved. By Hoeffding's inequality, the realized rewards are close to $\sum_{s,a} N(s,a)\bar r(s,a)$. Episodes in which the true MDP lies outside the confidence set contribute at most $\sqrt{T}$ with high probability, because the confidence sets fail at step $t$ with probability less than $\delta/(15t^6)$; that bound rests on the $\ell_1$ deviation inequality of Weissman, Ordentlich, Seroussi, Verdú and Weinberger, which no page of the graph states, so this theorem inherits that missing prerequisite through the confidence-set lemma. In the other episodes optimism gives $\tilde\rho_k \ge \rho^\star - 1/\sqrt{t_k}$, and the per-episode regret is at most $v_k(\tilde P_k - I)w_k$ plus confidence widths, where $w_k$ is the centered value iterate of extended value iteration, of sup norm at most $D/2$ by the span bound. Writing $\tilde P_k - I = (\tilde P_k - P_k) + (P_k - I)$, the first part is at most the $\ell_1$ width times $D/2$, and the second is a martingale handled by the Azuma–Hoeffding inequality plus $D$ per episode. Summing over at most $SA\log_2(8T/(SA))$ episodes, with $\sum_k v_k(s,a)/\sqrt{\max\{1, N_k(s,a)\}} \le (\sqrt2 + 1)\sqrt{N(s,a)}$, and taking a union bound over $T$ gives the result.

Besides the $\ell_1$ deviation inequality inherited through the confidence-set lemma, a good expansion adds pages for these steps of the proof, none of which the graph states:

- Theorem 7 of the source, proved in its Appendix B: if a set of MDPs of the form used by UCRL2 contains a communicating MDP, extended value iteration converges, and at its stopping rule the greedy policy is $\varepsilon$-optimal for the combined MDP. It gives $\tilde\rho_k \ge \rho^\star - 1/\sqrt{t_k}$ in each episode whose confidence set contains the true MDP. It is stated in prose on the [UCRL2 page](ucrl2-and-extended-value-iteration.md), which is a definition page, so it still needs a page of its own.
- The estimate (12), $\lvert u_{i+1}(s) - u_i(s) - \tilde\rho_k\rvert \le 1/\sqrt{t_k}$ for all $s$ at the stopping iteration, which the source takes from Puterman, *Markov Decision Processes* (1994), Theorem 8.5.6, and which turns the per-episode regret into $v_k(\tilde P_k - I)w_k$ plus confidence widths.
- Proposition 18 (at most $SA\log_2(8T/(SA))$ episodes up to step $T \ge SA$) and Lemma 19 (the bound $(\sqrt2 + 1)\sqrt{Z_n}$ on $\sum_k z_k/\sqrt{Z_{k-1}}$), both of Appendix C.

## Sources

- T. Jaksch, R. Ortner and P. Auer, "Near-optimal Regret Bounds for Reinforcement Learning", *Journal of Machine Learning Research* 11 (2010), 1563–1600: Theorem 2, Corollary 3, Theorem 4, Section 4 (proof of Theorem 2, inequalities (7) to (23) and Lemma 10), Section 8 (open problems), Theorem 7 with its proof in Appendix B, the estimate (12), Appendix C (Lemma 17, Proposition 18, Lemma 19). [PDF](https://www.jmlr.org/papers/volume11/jaksch10a/jaksch10a.pdf)
- P. Auer, T. Jaksch and R. Ortner, "Near-optimal Regret Bounds for Reinforcement Learning", *Advances in Neural Information Processing Systems 21* (NeurIPS 2008), the extended abstract of the journal paper, Theorem 2 there. [PDF](https://proceedings.neurips.cc/paper_files/paper/2008/file/e4a6222cdb5b34375400904f03d8e6a5-Paper.pdf)
- C. Jin, Z. Allen-Zhu, S. Bubeck and M. I. Jordan, "Is Q-learning Provably Efficient?", NeurIPS 2018, Table 1 and footnote 1 (UCRL2 applied to episodic MDPs). [PDF](https://proceedings.neurips.cc/paper_files/paper/2018/file/d3b1fb02964aa64e257f9f26a31f72cf-Paper.pdf)
