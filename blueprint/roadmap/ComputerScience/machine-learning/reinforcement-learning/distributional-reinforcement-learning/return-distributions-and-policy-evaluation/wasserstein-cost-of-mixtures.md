# Wasserstein cost of mixtures with common weights

Mixing two families of laws with the same weights costs at most the weighted average of the $p$-th power Wasserstein costs. Then the corrected partition lemma of Bellemare, Dabney and Munos, stated with conditional laws, holds.

Let $1 \le p < \infty$, let $I$ be a finite index set, let $w_i \ge 0$ with $\sum_{i \in I} w_i = 1$, and let $\nu_i, \mu_i$ be Borel probability measures on $\mathbb{R}$. With $W_p$ the [Wasserstein distance of order $p$](../../../../../MeasureTheory/optimal-transport/wasserstein-distances/wasserstein-distance/wasserstein.md),

$$W_p^p\Bigl(\sum_{i \in I} w_i \nu_i, \; \sum_{i \in I} w_i \mu_i\Bigr) \le \sum_{i \in I} w_i \, W_p^p(\nu_i, \mu_i)$$

in $[0, \infty]$. Equivalently, if $A_i$, $i \in I$, are events partitioning a probability space with $\Pr(A_i) > 0$ and $U, V$ are real random variables, then

$$W_p^p\bigl(\mathrm{Law}(U), \mathrm{Law}(V)\bigr) \le \sum_{i \in I} \Pr(A_i) \, W_p^p\bigl(\mathrm{Law}(U \mid A_i), \mathrm{Law}(V \mid A_i)\bigr).$$

## Depends on

- [Wasserstein distance of order p](../../../../../MeasureTheory/optimal-transport/wasserstein-distances/wasserstein-distance/wasserstein.md)
- [Law of a random element](../../../../../Probability/foundations/probability-measures/probability-measure-map.md)

## Proof depends on

- [Wasserstein distance of order p](../../../../../MeasureTheory/optimal-transport/wasserstein-distances/wasserstein-distance/wasserstein.md)
- [Every coupling bounds the Wasserstein distance](../../../../../MeasureTheory/optimal-transport/wasserstein-distances/wasserstein-distance/wasserstein-le-of-is-coupling.md)

## Expansion

If the right side is finite, fix $\varepsilon > 0$ and choose, for each $i$ with $w_i > 0$, a coupling $\pi_i$ of $\nu_i$ and $\mu_i$ whose cost $\int |s - t|^p \, d\pi_i$ is at most $W_p^p(\nu_i, \mu_i) + \varepsilon$. Then $\sum_i w_i \pi_i$ is a coupling of the two mixtures, its cost is at most the right side plus $\varepsilon$, and [every coupling bounds the Wasserstein distance](../../../../../MeasureTheory/optimal-transport/wasserstein-distances/wasserstein-distance/wasserstein-le-of-is-coupling.md). Indices with $w_i = 0$ contribute nothing. The random-variable form is the case $w_i = \Pr(A_i)$, $\nu_i = \mathrm{Law}(U \mid A_i)$, $\mu_i = \mathrm{Law}(V \mid A_i)$, since $\mathrm{Law}(U) = \sum_i \Pr(A_i) \mathrm{Law}(U \mid A_i)$. The same proof works for a countable index set. Only finitely many couplings are chosen, so no measurable selection is needed.

**What the source states.** Bellemare, Dabney and Munos's Lemma 1 (the partition lemma) states $d_p(U, V) \le \sum_i d_p(A_i U, A_i V)$ for indicator random variables $A_i$ of a partition, where the products $A_i U$ carry an extra atom at $0$ of mass $\Pr(A_i = 0)$. That statement fails for every $p > 1$. Take two equally likely outcomes $\omega_1, \omega_2$, $A_1 = \mathbf{1}_{\{\omega_1\}}$, $A_2 = \mathbf{1}_{\{\omega_2\}}$, $U(\omega_1) = -1$, $V(\omega_1) = 1$ and $U(\omega_2) = V(\omega_2) = 5$. Then $A_1 U$ and $A_1 V$ have laws $\frac12 \delta_{-1} + \frac12 \delta_0$ and $\frac12 \delta_0 + \frac12 \delta_1$, at $W_p$-distance $1$ (the monotone coupling, cost $\frac12 + \frac12$, is optimal: a coupling moving mass $\frac12 - a$ from $-1$ to $1$ costs $2a + (\frac12 - a) 2^p \ge 1$). Next, $A_2 U$ and $A_2 V$ both have law $\frac12 \delta_0 + \frac12 \delta_5$. But $U$ and $V$ have laws $\frac12 \delta_{-1} + \frac12 \delta_5$ and $\frac12 \delta_1 + \frac12 \delta_5$, at $W_p$-distance $2^{1 - 1/p} > 1$ for $p > 1$. The $p$-th power inequality that the source's proof arrives at, $d_p^p(U,V) \le \sum_i d_p^p(A_i U, A_i V)$, fails on the same example ($2^{p-1} > 1$). The defect is the step that assumes an optimal coupling of $A_i U$ and $A_i V$ matches their atoms at $0$. The inequality on this page uses the conditional laws on $A_i$ instead of the laws of the products, and that is the form the contraction of the distributional Bellman operator needs. For $p = 1$ the source's stated form is true, because $W_1$ is the $L^1$ distance between distribution functions and $F_U - F_V = \sum_i (F_{A_i U} - F_{A_i V})$; no page here uses that case.

## Sources

- M. G. Bellemare, W. Dabney and R. Munos, *A Distributional Perspective on Reinforcement Learning*, Proceedings of the 34th International Conference on Machine Learning (ICML 2017); numbers from arXiv:1707.06887v1, <https://arxiv.org/abs/1707.06887v1>: Section 3.2, Lemma 1 (partition lemma) and its proof in Appendix B, which works with $p$-th powers and conditional laws.
