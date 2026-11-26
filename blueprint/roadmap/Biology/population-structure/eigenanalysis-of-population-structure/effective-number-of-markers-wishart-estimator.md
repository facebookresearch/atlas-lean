# Method-of-moments estimator for effective number of markers in a Wishart matrix

Let $M \in \mathbb{R}^{m \times n}$ have i.i.d. $\mathcal{N}(0, \sigma^2)$ entries, and let
$\lambda_1, \dots, \lambda_m$ be the eigenvalues of the $m \times m$ Wishart matrix $X = M M^\top$.
Define the first two empirical eigenvalue sums

$$L_1 = \sum_{i=1}^m \lambda_i = \operatorname{tr}(X), \qquad L_2 = \sum_{i=1}^m \lambda_i^2 = \operatorname{tr}(X^2).$$

Then $\mathbb{E}[L_1] = m n \sigma^2$ and $\mathbb{E}[L_2] = m n (m + n + 1) \sigma^4$.
Consequently, when $n$ and $\sigma^2$ are unknown, the method-of-moments estimators

$$\hat n' = \frac{(m + 1) L_1^2}{m L_2 - L_1^2}, \qquad \hat\sigma^2 = \frac{L_1}{m \hat n'}$$

satisfy $L_1 = m \hat n' \hat\sigma^2$ and $L_2 = m \hat n' (m + \hat n' + 1) \hat\sigma^4$,
matching both observed eigenvalue sums to their Wishart expectations.

## Expansion

Since $X = M M^\top$ has $\mathbb{E}[X_{ii}] = n\sigma^2$, $\mathbb{E}[X_{ii}^2] = n(n+2)\sigma^4$,
and $\mathbb{E}[X_{ij}^2] = n\sigma^4$ for $i \ne j$, summing over the $m$ diagonal and
$m(m-1)$ off-diagonal entries gives $\mathbb{E}[\operatorname{tr}(X)] = mn\sigma^2$ and
$\mathbb{E}[\operatorname{tr}(X^2)] = m n(n+2)\sigma^4 + m(m-1)n\sigma^4 = mn(m+n+1)\sigma^4$.
Solving the two moment equations for $(n, \sigma^2)$ yields $\hat n'$ and $\hat\sigma^2$.

## Sources

- N. Patterson, A. L. Price, and D. Reich, "Population Structure and Eigenanalysis", PLOS Genetics 2 (2006), e190, <https://doi.org/10.1371/journal.pgen.0020190> (PMC1713260). (Theorem 1.)
