# Modified FDR control by knockoff

Let $\mu$ be a probability measure on $\Omega$, $W : \Omega \to \mathbb{R}^p$ measurable statistics and $H_0 \subseteq \{1, \dots, p\}$ the set of null variables, and suppose that flipping the signs of any set $S \subseteq H_0$ of null statistics leaves the law of $W$ unchanged (the hypotheses of [FDR control by knockoff+](integral-false-discovery-proportion-knoc.md)). Then for $0 < q \le 1$ the knockoff selection $\hat S = \{j : W_j \ge T_0\}$ (offset $0$) satisfies

$$\mathbb{E}\Big[\frac{|\hat S \cap H_0|}{|\hat S| + q^{-1}}\Big] \le q.$$

The source proves Theorems 1 and 2 with the same sequential (supermartingale) argument; its proof sketch treats knockoff+.

## Background

- [FDR control by knockoff+](integral-false-discovery-proportion-knoc.md): the companion statement with the $+1$ correction, which controls the usual FDR.

## Sources

- R. F. Barber and E. J. Candès, *Controlling the false discovery rate via knockoffs*, Ann. Statist. 43 (2015), arXiv:1404.5609, Theorem 1 (stated for $q \in [0, 1]$; the statement above assumes $0 < q$, which keeps $q^{-1}$ finite), through Lemma 1; E. Candès, Y. Fan, L. Janson and J. Lv, J. R. Statist. Soc. B 80 (2018), arXiv:1610.02351, Theorem 3.4 (knockoff part) with Lemma 3.3.
