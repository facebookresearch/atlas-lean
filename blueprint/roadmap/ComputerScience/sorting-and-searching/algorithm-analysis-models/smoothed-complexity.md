# Smoothed complexity

Let $A$ be an algorithm on inputs $x \in \mathbb{R}^N$ with cost $c_A(x)$. Its *smoothed complexity* is $C_A(n, \sigma) = \sup_{\|x\| \le 1} \mathbb{E}_g[c_A(x + \sigma g)]$, where the supremum is over normalized inputs of size $n$, $g$ has independent standard Gaussian entries, and $c_A$ is assumed measurable so that the expectations are defined (possibly infinite). If $c_A$ is continuous and bounded by a polynomial in $\|x\|$, then $C_A(n, \sigma)$ tends to the worst-case cost $\sup_{\|x\| \le 1} c_A(x)$ as $\sigma \to 0$. Neither hypothesis can be dropped: a cost spike on a null set is invisible to every $\sigma > 0$, and the continuous cost $e^{\|x\|^4}$ has infinite Gaussian expectation for every $\sigma > 0$. $A$ has polynomial smoothed complexity if $C_A(n, \sigma) \le \mathrm{poly}(n, 1/\sigma)$.

## Depends on

- [Expected running time](../../randomized-algorithms/average-case-running-time/expected-time.md)

## Sources

- D. A. Spielman and S.-H. Teng, "Smoothed analysis of algorithms: why the simplex algorithm usually takes polynomial time", *Journal of the ACM* 51(3):385–463, 2004
