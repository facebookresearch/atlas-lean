# UCRL2 confidence sets contain the true MDP with high probability

At every step $t \ge 1$, the probability that the true MDP lies outside the set of MDPs that UCRL2 considers plausible at step $t$ is less than $\delta/(15t^6)$. Summed over $t$, this bounds the regret contributed by episodes whose confidence set fails.

Let $M$ be an MDP with $S$ states, $A$ actions, rewards drawn independently from distributions on $[0, 1]$ with means $\bar r(s, a)$, and transition laws $p(\cdot \mid s, a)$, and let $\delta \in (0, 1)$. For $t \ge 1$ let $\mathcal{M}(t)$ be the set of plausible MDPs that [UCRL2](ucrl2-and-extended-value-iteration.md) forms from the observations before step $t$: rewards $\tilde r(s, a) \in [0, 1]$ and transition laws $\tilde p(\cdot \mid s, a)$ with

$$
|\tilde r(s, a) - \hat r(s, a)| \le \sqrt{\frac{7\log(2SAt/\delta)}{2\max\{1, N(s, a)\}}}, \qquad \big\lVert \tilde p(\cdot \mid s, a) - \hat p(\cdot \mid s, a)\big\rVert_1 \le \sqrt{\frac{14S\log(2At/\delta)}{\max\{1, N(s, a)\}}},
$$

where $N(s, a)$ is the number of visits to $(s, a)$ before step $t$ and $\hat r$, $\hat p$ are the empirical estimates. Then for every $t \ge 1$

$$
\Pr\big[M \notin \mathcal{M}(t)\big] < \frac{\delta}{15t^6}.
$$

## Depends on

- [UCRL2 and extended value iteration](ucrl2-and-extended-value-iteration.md)

## Proof depends on

- [Two-sided Hoeffding inequality for averages of bounded variables](../../../../Probability/concentration-inequalities/hoeffding-s-inequality/measure-real-abs-avg-sub-ge-le.md)

## Expansion

Fix $(s, a)$ and a number $n \ge 1$ of earlier visits. For the transitions, the $\ell_1$ deviation inequality for empirical distributions of Weissman, Ordentlich, Seroussi, Verdú and Weinberger, in the form $\Pr[\lVert \hat p - p\rVert_1 \ge \varepsilon] \le (2^m - 2)\exp(-n\varepsilon^2/2)$ for $m$ outcomes and $n$ i.i.d. samples, with $m = S$ and $\varepsilon = \sqrt{\frac2n\log\frac{2^S 20SAt^7}{\delta}} \le \sqrt{\frac{14S}{n}\log\frac{2At}{\delta}}$, gives failure probability at most $\delta/(20t^7SA)$. For the rewards, the two-sided Hoeffding inequality $\Pr[\lvert\hat r - \bar r\rvert \ge \varepsilon_r] \le 2e^{-2n\varepsilon_r^2}$ for $n$ i.i.d. samples in $[0, 1]$ with $\varepsilon_r = \sqrt{\frac{1}{2n}\log\frac{120SAt^7}{\delta}} \le \sqrt{\frac{7}{2n}\log\frac{2SAt}{\delta}}$ gives failure probability at most $\delta/(60t^7SA)$. A union bound over the state-action pairs and the possible values of $n$ before step $t$ gives the claim.

That form follows from Theorem 2.1 of Weissman and coauthors, $\Pr[\lVert p - \hat p\rVert_1 \ge \varepsilon] \le (2^m - 2)e^{-n\varphi(\pi_p)\varepsilon^2/4}$ (their inequality (8)), since $\varphi(\pi_p) \ge 2$ (their Proposition 4.3). No page of the graph states this inequality, so this lemma has a missing proof prerequisite. Applied with $t = t_k$, the lemma is what makes the episodes with $M \notin \mathcal{M}_k$ contribute at most $\sqrt{T}$ to the [UCRL2 regret bound](ucrl2-regret-bound.md), with high probability.

## Sources

- T. Jaksch, R. Ortner and P. Auer, "Near-optimal Regret Bounds for Reinforcement Learning", *Journal of Machine Learning Research* 11 (2010), 1563–1600: Lemma 17 and its proof in Appendix C.1, including the deviation inequality (44); the confidence sets (3) and (4) in Figure 1. [PDF](https://www.jmlr.org/papers/volume11/jaksch10a/jaksch10a.pdf)
- T. Weissman, E. Ordentlich, G. Seroussi, S. Verdú and M. J. Weinberger, "Inequalities for the L1 Deviation of the Empirical Distribution", Technical Report HPL-2003-97 (R.1), HP Laboratories Palo Alto, 2003, Theorem 2.1, inequality (8), with Proposition 4.3 ($\varphi(\pi_P) \ge 2$). [PDF](https://web.archive.org/web/20220123001144/https://www.hpl.hp.com/techreports/2003/HPL-2003-97R1.pdf)
