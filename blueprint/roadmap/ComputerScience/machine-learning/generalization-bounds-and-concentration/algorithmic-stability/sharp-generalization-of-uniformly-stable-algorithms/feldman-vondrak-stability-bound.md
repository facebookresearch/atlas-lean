# Feldman–Vondrák high-probability bound for uniformly stable algorithms

Let $A$ be $\gamma$-uniformly stable with loss bounded in $[0,1]$. Then with probability at least $1 - \delta$ over $S \sim D^n$,

$$
\big|R(A_S) - R_{\mathrm{emp}}(A_S)\big| \le O\!\left(\gamma\log(n)\log\frac{en}{\delta} + \sqrt{\frac{\log(e/\delta)}{n}}\right).
$$

Logarithms of the confidence parameter follow the convention of Bousquet, Klochkov and Zhivotovskiy (§2.1), which floors them at $1$: $\log(e/\delta) = 1 + \log(1/\delta)$ lies between $\max\{1, \log(1/\delta)\}$ and twice it, so the right-hand side stays bounded away from $0$ as $\delta \to 1$.

Like the earlier bound of Feldman and Vondrák (NeurIPS 2018), it shows that $\gamma = o(1/\sqrt{n})$ is not needed for nontrivial high-probability generalization (the Bousquet–Elisseeff bound $O(\gamma\sqrt{n\log(e/\delta)} + \sqrt{\log(e/\delta)/n})$ is vacuous for $\gamma \gtrsim 1/\sqrt{n}$); the later bound of Bousquet, Klochkov and Zhivotovskiy removes one logarithmic factor.

## Proof sketch

Split the sample recursively into halves; on each level, use uniform stability to compare the algorithm's output with outputs on disjoint subsamples and control the deviation by concentration of functions with bounded differences on independent blocks, accumulating a factor $\gamma$ per level over $\log n$ levels. A clipping argument handles the dependence across levels, giving the $\log(n)\log(n/\delta)$ factor.

## Depends on

- [Uniform stability](../is-uniformly-stable.md)
- [Expected risk](../../risk.md)
- [Empirical risk](../../empirical-risk.md)

## Proof depends on

- [Moment form of the bounded differences inequality](bounded-differences-moment-inequality.md)

## Sources

- V. Feldman, J. Vondrak, "High Probability Generalization Bounds for Uniformly Stable Algorithms with Nearly Optimal Rate", COLT (2019), arXiv:1902.10710.
- V. Feldman, J. Vondrak, "Generalization Bounds for Uniformly Stable Algorithms", NeurIPS (2018), arXiv:1812.09859.
- O. Bousquet, A. Elisseeff, "Stability and Generalization", Journal of Machine Learning Research 2 (2002).
