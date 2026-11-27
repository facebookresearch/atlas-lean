# Selberg's upper bound with the optimal level weights

Take a bounding sieve: a finite weighted set to be sifted by the primes dividing a squarefree $P$, with total weight approximated by $X$, density function $\nu$ and remainders $r_d = A_d - \nu(d) X$. Let $R \ge 1$ be a natural number, $\lambda_d$ the [level-$R$ Selberg weights](level-weights.md) and $\Lambda_d = \sum_{\operatorname{lcm}(d_1, d_2) = d} \lambda_{d_1} \lambda_{d_2}$. Then the sifted sum $S$ satisfies

$$S \le \frac{X}{G(R)} + \sum_{d \mid P} |\Lambda_d|\, |r_d|,$$

where $G(R)$ is the [level sum](level-sum.md).

This is Heath-Brown's inequality (2.5), $S(\mathcal A, \mathcal P; z) \le X\, G(\xi, z)^{-1} + \sum_{d \mid \Pi(\mathcal P, z),\, d < y} |\mu^+(d)|\, |R_d|$, with the support condition $\lambda_d = 0$ for $d > R$ in place of (2.4)'s $\lambda_d = 0$ for $d \ge \xi$, and the density $\nu(d)$ in place of $\omega(d)/d$.

## Background

- [Error bound for the Selberg level weights](level-weights-err-sum-le.md): bounds the error sum by $R^{12}$ when $d\,\nu(d) \ge 1$ and $|r_d| \le d$.
- [Selberg's $\Lambda^2$ upper bound sieve, finite form](card-filter-coprime-le-sum-lambda-sq.md): the unweighted bound for arbitrary $\lambda_d$.

## Sources

- D. R. Heath-Brown, "Lectures on sieves", arXiv:math/0209360 (2002), Sections 1–2.
