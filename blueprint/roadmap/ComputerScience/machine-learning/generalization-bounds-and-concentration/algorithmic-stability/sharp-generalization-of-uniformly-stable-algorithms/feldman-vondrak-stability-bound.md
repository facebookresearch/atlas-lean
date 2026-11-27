# Feldman–Vondrák high-probability bound for uniformly stable algorithms

Let $A$ be $\gamma$-uniformly stable with loss bounded in $[0,1]$. Then with probability at least $1 - \delta$ over $S \sim D^n$,

$$
\big|R(A_S) - R_{\mathrm{emp}}(A_S)\big| \le O\!\left(\gamma\log(n)\log\frac{en}{\delta} + \sqrt{\frac{\log(e/\delta)}{n}}\right).
$$

Logarithms of the confidence parameter follow the convention of Bousquet, Klochkov and Zhivotovskiy (§2.1), which floors them at $1$: $\log(e/\delta) = 1 + \log(1/\delta)$ lies between $\max\{1, \log(1/\delta)\}$ and twice it, so the right-hand side stays bounded away from $0$ as $\delta \to 1$.

Like the earlier bound of Feldman and Vondrák (NeurIPS 2018), it shows that $\gamma = o(1/\sqrt{n})$ is not needed for nontrivial high-probability generalization (the Bousquet–Elisseeff bound $O(\gamma\sqrt{n\log(e/\delta)} + \sqrt{\log(e/\delta)/n})$ is vacuous for $\gamma \gtrsim 1/\sqrt{n}$); the later bound of Bousquet, Klochkov and Zhivotovskiy removes one logarithmic factor.

## Proof sketch

Two reductions are applied recursively. Dataset size reduction: partitioning the sample into blocks of size $n' = n/b$, the estimation error is an average of block averages, and each block average, conditioned on the other blocks, is the estimation error of a problem with $n'$ samples and the same stability parameter. Range reduction: by McDiarmid's inequality the function concentrates in a window of size $\gamma\sqrt{n}$ around its mean over samples, so after subtracting that mean it is clamped to such a range, by a data-dependent clamp that preserves both the stability parameter and the zero mean of the estimation error. Alternating the two reductions returns to a problem with stability equal to range over the square root of the sample size; the $\log n$ levels of this recursion give the $\log n$ overhead.

## Depends on

- [Uniform stability](../is-uniformly-stable.md)
- [Expected risk](../../risk.md)
- [Empirical risk](../../empirical-risk.md)

## Proof depends on

- [McDiarmid's inequality, upper tail](../../../../../Probability/concentration-inequalities/mcdiarmid-s-inequality/measure-real-sub-integral-ge-le-of-bound.md)
- [McDiarmid's inequality, lower tail](../../../../../Probability/concentration-inequalities/mcdiarmid-s-inequality/measure-real-integral-sub-ge-le-of-bound.md)

## Sources

- V. Feldman, J. Vondrak, "High Probability Generalization Bounds for Uniformly Stable Algorithms with Nearly Optimal Rate", COLT (2019), arXiv:1902.10710, Theorem 1.1.
- V. Feldman, J. Vondrak, "Generalization Bounds for Uniformly Stable Algorithms", NeurIPS (2018), arXiv:1812.09859.
- O. Bousquet, A. Elisseeff, "Stability and Generalization", Journal of Machine Learning Research 2 (2002).
