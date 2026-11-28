# Moment inequality for sums of weakly correlated functions

Let $Z = (Z_1, \dots, Z_n)$ be independent random variables and $g_1, \dots, g_n : \mathcal{Z}^n \to \mathbb{R}$ functions such that for every $i$: $|\mathbb{E}[g_i(Z) \mid Z_i]| \le M$ almost surely, $\mathbb{E}[g_i(Z) \mid Z_{[n] \setminus \{i\}}] = 0$ almost surely, and $g_i$ has bounded differences $\beta$ with respect to every coordinate other than the $i$-th. Then for every $p \ge 2$

$$
\Big\| \sum_{i=1}^n g_i(Z) \Big\|_p \le 12\sqrt{2}\, p\, n \beta \lceil \log_2 n \rceil + 4 M \sqrt{p n},
$$

where $\|Y\|_p = (\mathbb{E}|Y|^p)^{1/p}$.

## Proof sketch

Assume $n = 2^k$ and consider the dyadic partitions $B_0, \dots, B_k$ of $[n]$. Telescope $g_i$ through conditional expectations given the blocks of successive partitions; at each of the $\log_2 n$ levels the block-conditional terms form sums of functions of disjoint blocks to which the moment version of McDiarmid's inequality $\|f - \mathbb{E}f\|_p \le 2\sqrt{np}\beta$ applies, contributing $O(p n\beta)$ per level, while the final term is a sum of independent centred variables bounded via Marcinkiewicz–Zygmund by $O(M\sqrt{pn})$.

## Proof depends on

- [Moment form of the bounded differences inequality](bounded-differences-moment-inequality.md)

## Sources

- O. Bousquet, Y. Klochkov, N. Zhivotovskiy, "Sharper Bounds for Uniformly Stable Algorithms", COLT (2020), arXiv:1910.07833, Theorem 4.
