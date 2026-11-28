# Packing lower bounds for zCDP

Let $M : \mathcal{X}^n \to \mathcal{Y}$ be $\rho$-zCDP and let $S_1, \dots, S_m \in \mathcal{X}^n$ be datasets of size $n$. If there are pairwise disjoint events $E_1, \dots, E_m$ with $\Pr[M(S_i) \in E_i] \ge 1/2$ for every $i$, then, for $m$ larger than an absolute constant,

$$
\rho\, n^2 \ge \Omega(\log m).
$$

In particular, releasing a histogram over a universe of size $N$ (or answering point queries) to constant accuracy under $\rho$-zCDP requires $n = \Omega\big(\sqrt{\log N / \rho}\big)$ records, a lower bound of the same form as for pure differential privacy and impossible for approximate differential privacy, where $O(\log(1/\delta)/\varepsilon)$ records suffice.

## Proof sketch

Any two datasets in $\mathcal{X}^n$ differ in at most $n$ entries, so by group privacy $D_\alpha(M(S_i) \| M(S_j)) \le n^2\rho\alpha$ for all pairs. Taking $\alpha \to 1$, the Kullback–Leibler divergences are at most $n^2\rho$, so the mutual information between a uniformly random index $I$ and $M(S_I)$ is at most $n^2\rho$; Fano's inequality with the disjoint decoding events requires mutual information $\Omega(\log m)$. Bun and Steinke's Lemma 7.4 states the explicit form $(1-\beta)\log m - \log 2 \le \rho n^2$ when each $S_i$ is decoded correctly with probability at least $1 - \beta$; here $\beta = 1/2$. For histograms, take the $N$ datasets concentrating all $n$ records on a single element, so $m = N$.

## Depends on

- [Zero-concentrated differential privacy](zero-concentrated-dp.md)

## Proof depends on

- [Group privacy for zCDP scales quadratically](zcdp-group-privacy.md)
- [Fano's inequality, general form](../../../../InformationTheory/information-inequalities/fano-s-inequality/fano-inequality-general.md)

## Sources

- M. Bun, T. Steinke, "Concentrated Differential Privacy: Simplifications, Extensions, and Lower Bounds", TCC (2016), arXiv:1605.02065, Theorem 1.10, Section 6 and Lemma 7.4.
