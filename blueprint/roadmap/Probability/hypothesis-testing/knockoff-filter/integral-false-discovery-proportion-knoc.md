# FDR control by knockoff+

Let $\mu$ be a probability measure on $\Omega$, $W : \Omega \to \mathbb{R}^p$ measurable statistics and $H_0 \subseteq \{1, \dots, p\}$ the set of null variables, and suppose that flipping the signs of any set $S \subseteq H_0$ of null statistics leaves the law of $W$ unchanged. Then for $0 \le q \le 1$ the knockoff+ selection $\hat S = \{j : W_j \ge T_1\}$ has false discovery rate at most $q$:

$$\mathbb{E}\Big[\frac{|\hat S \cap H_0|}{\max(|\hat S|, 1)}\Big] \le q.$$

The source's proof bounds the false discovery proportion at the threshold $T$ by $q\, V^+(T) / (1 + V^-(T))$, the null counts above $T$ and below $-T$, and shows that $V^+(t) / (1 + V^-(t))$ is a supermartingale in $t$ for which $T$ is a stopping time, so its expectation at $T$ is at most $1$; only the fair signs of the null statistics are used.

## Informally uses

- [The false discovery proportion of knockoff+ is bounded by a null-count ratio](false-discovery-proportion-knockoff-sele.md): the deterministic first step, equation (2.5) of the source.

## Background

- [Benjamini–Hochberg FDR control](../benjamini-hochberg-procedure/integral-false-discovery-proportion-bh-r.md): FDR control from independent valid p-values, the guarantee knockoff+ matches without p-values.

## Sources

- R. F. Barber and E. J. Candès, *Controlling the false discovery rate via knockoffs*, Ann. Statist. 43 (2015) 2055-2085, arXiv:1404.5609, Theorem 2, through Lemma 1 (i.i.d. signs for the nulls), which is the only property of $W$ its proof uses; E. Candès, Y. Fan, L. Janson and J. Lv, *Panning for gold: model-X knockoffs for high dimensional controlled variable selection*, J. R. Statist. Soc. B 80 (2018), arXiv:1610.02351, Theorem 3.4 (knockoff+ part) with Lemma 3.3.
