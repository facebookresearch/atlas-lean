# High-probability generalization of uniformly stable algorithms with a single logarithmic factor

Let $A$ be a learning algorithm that is $\gamma$-uniformly stable (replacing one of $n$ examples changes the loss of the output on every point by at most $\gamma$) with a loss taking values in $[0, L]$, and let $S = (Z_1, \dots, Z_n) \sim D^n$ be an i.i.d. sample. Then for every $\delta \in (0,1)$, with probability at least $1-\delta$ over $S$,

$$
\big| R(A_S) - R_{\mathrm{emp}}(A_S) \big| \lesssim \gamma \log n \log\frac{e}{\delta} + L \sqrt{\frac{\log(e/\delta)}{n}},
$$

where $R(h) = \mathbb{E}_{Z \sim D}[\ell(h, Z)]$ is the population risk over a fresh draw $Z \sim D$ independent of $S$, $R_{\mathrm{emp}}$ is the empirical risk on $S$, and $\lesssim$ hides an absolute constant. Without independence the bound fails: $n$ copies of one fair bit give gap $\tfrac12$ at stability zero. Logarithms of the confidence parameter follow the convention of Bousquet, Klochkov and Zhivotovskiy (§2.1), which floors them at $1$: $\log(e/\delta) = 1 + \log(1/\delta)$ lies between $\max\{1, \log(1/\delta)\}$ and twice it, so the right-hand side stays bounded away from $0$ as $\delta \to 1$. This improves the Bousquet–Elisseeff bound $O(\gamma\sqrt{n\log(e/\delta)} + L\sqrt{\log(e/\delta)/n})$ and removes a $\log n$ factor from the Feldman–Vondrák bound.

## Proof sketch

Up to an additive $O(n\gamma)$ term, write $n(R(A_S) - R_{\mathrm{emp}}(A_S)) = \sum_i g_i(S)$ with $g_i(S) = \mathbb{E}_{Z_i'}\big[\mathbb{E}_{Z}[\ell(A_{S^{(i)}}, Z)] - \ell(A_{S^{(i)}}, Z_i)\big]$, where $S^{(i)}$ replaces $Z_i$ by an independent copy $Z_i'$; these functions satisfy the conditional mean-zero property, are bounded by $L$, and have bounded differences $2\gamma$ in the other coordinates by uniform stability. The moment inequality for weakly correlated sums gives $\|\sum_i g_i\|_p \lesssim p n\gamma \log n + L\sqrt{pn}$, for every $p \ge 2$, and the mixed tail lemma with $p_\delta = \max\{2, \log(e/\delta)\} \le 2\log(e/\delta)$ gives the tail bound.

## Depends on

- [Uniform stability](../is-uniformly-stable.md)
- [Expected risk](../../risk.md)
- [Empirical risk](../../empirical-risk.md)

## Proof depends on

- [Moment inequality for sums of weakly correlated functions](weakly-correlated-sum-moment-inequality.md)
- [Mixed moment growth implies mixed sub-exponential tails](moment-growth-to-tail-bound.md)

## Sources

- O. Bousquet, Y. Klochkov, N. Zhivotovskiy, "Sharper Bounds for Uniformly Stable Algorithms", COLT (2020), arXiv:1910.07833.
- V. Feldman, J. Vondrak, "High Probability Generalization Bounds for Uniformly Stable Algorithms with Nearly Optimal Rate", COLT (2019), arXiv:1902.10710.
- O. Bousquet, A. Elisseeff, "Stability and Generalization", Journal of Machine Learning Research 2 (2002).
