# Feldman–Vondrák high-probability bound for uniformly stable algorithms

Let $A$ be $\gamma$-uniformly stable with loss bounded in $[0,1]$. Then with probability at least $1 - \delta$ over $S \sim D^n$,

$$
\big|R(A_S) - R_{\mathrm{emp}}(A_S)\big| \le O\!\left(\gamma\log(n)\log\frac{n}{\delta} + \sqrt{\frac{\log(1/\delta)}{n}}\right).
$$

This was the first bound showing that $\gamma = o(1/\sqrt{n})$ is not needed for nontrivial high-probability generalization (the Bousquet–Elisseeff bound $O(\gamma\sqrt{n\log(1/\delta)} + \sqrt{\log(1/\delta)/n})$ is vacuous for $\gamma \gtrsim 1/\sqrt{n}$); the later bound of Bousquet, Klochkov and Zhivotovskiy removes one logarithmic factor.

## Proof sketch

Split the sample recursively into halves; on each level, use uniform stability to compare the algorithm's output with outputs on disjoint subsamples and control the deviation by concentration of functions with bounded differences on independent blocks, accumulating a factor $\gamma$ per level over $\log n$ levels. A clipping argument handles the dependence across levels, giving the $\log(n)\log(n/\delta)$ factor.

## Depends on

- [Uniform stability implies high-probability generalization](../algorithmic-stability/uniform-stability-implies-high-probability-generalization.md)
- [Moment form of the bounded differences inequality](bounded-differences-moment-inequality.md)

## Proof depends on

- [Uniform stability implies high-probability generalization](../algorithmic-stability/uniform-stability-implies-high-probability-generalization.md)
- [Moment form of the bounded differences inequality](bounded-differences-moment-inequality.md)

## Sources

- V. Feldman, J. Vondrak, "High Probability Generalization Bounds for Uniformly Stable Algorithms with Nearly Optimal Rate", COLT (2019), arXiv:1902.10710.
- O. Bousquet, A. Elisseeff, "Stability and Generalization", Journal of Machine Learning Research 2 (2002).
