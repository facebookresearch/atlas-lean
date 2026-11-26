# High-probability generalization of uniformly stable algorithms with a single logarithmic factor

Let $A$ be a learning algorithm that is $\gamma$-uniformly stable (replacing one of $n$ examples changes the loss of the output on every point by at most $\gamma$) with loss bounded by $L$. Then for every $\delta \in (0,1)$, with probability at least $1-\delta$ over the sample $S$,

$$
\big| R(A_S) - R_{\mathrm{emp}}(A_S) \big| \lesssim \gamma \log n \log\frac{1}{\delta} + L \sqrt{\frac{\log(1/\delta)}{n}},
$$

where $R$ and $R_{\mathrm{emp}}$ are the population and empirical risks and $\lesssim$ hides an absolute constant. This improves the Bousquet–Elisseeff bound $O(\gamma\sqrt{n\log(1/\delta)} + L\sqrt{\log(1/\delta)/n})$ and removes a $\log n$ factor from the Feldman–Vondrák bound.

## Proof sketch

Up to an additive $O(n\gamma)$ term, write $n(R(A_S) - R_{\mathrm{emp}}(A_S)) = \sum_i g_i(S)$ with $g_i(S) = \mathbb{E}_{Z_i'}\big[\mathbb{E}_{Z}[\ell(A_{S^{(i)}}, Z)] - \ell(A_{S^{(i)}}, Z_i)\big]$, where $S^{(i)}$ replaces $Z_i$ by an independent copy $Z_i'$; these functions satisfy the conditional mean-zero property, are bounded by $L$, and have bounded differences $2\gamma$ in the other coordinates by uniform stability. The moment inequality for weakly correlated sums gives $\|\sum_i g_i\|_p \lesssim p n\gamma \log n + L\sqrt{pn}$, and Markov's inequality with $p = \log(1/\delta)$ gives the tail bound.

## Depends on

- [Moment inequality for sums of weakly correlated functions](weakly-correlated-sum-moment-inequality.md)
- [Uniform stability](../algorithmic-stability/is-uniformly-stable.md)
- [Uniform stability implies high-probability generalization](../algorithmic-stability/uniform-stability-implies-high-probability-generalization.md)

## Proof depends on

- [Moment inequality for sums of weakly correlated functions](weakly-correlated-sum-moment-inequality.md)
- [Uniform stability](../algorithmic-stability/is-uniformly-stable.md)
- [Uniform stability implies high-probability generalization](../algorithmic-stability/uniform-stability-implies-high-probability-generalization.md)

## Sources

- O. Bousquet, Y. Klochkov, N. Zhivotovskiy, "Sharper Bounds for Uniformly Stable Algorithms", COLT (2020), arXiv:1910.07833.
- V. Feldman, J. Vondrak, "High Probability Generalization Bounds for Uniformly Stable Algorithms with Nearly Optimal Rate", COLT (2019), arXiv:1902.10710.
- O. Bousquet, A. Elisseeff, "Stability and Generalization", Journal of Machine Learning Research 2 (2002).
