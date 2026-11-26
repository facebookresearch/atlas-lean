# Method-of-moments estimator for effective number of markers in a Wishart matrix

Let $\sigma^2 \ge 0$, let $M \in \mathbb{R}^{m \times n}$ have i.i.d. $\mathcal{N}(0, \sigma^2)$ entries, and let
$\lambda_1, \dots, \lambda_m$ be the eigenvalues of the $m \times m$ uncentred Wishart matrix $X = M M^\top$.
Define the first two eigenvalue sums

$$L_1 = \sum_{i=1}^m \lambda_i = \operatorname{tr}(X), \qquad L_2 = \sum_{i=1}^m \lambda_i^2 = \operatorname{tr}(X^2).$$

Then

$$\mathbb{E}[L_1] = m n \sigma^2, \qquad \mathbb{E}[L_2] = m n (m + n + 1) \sigma^4, \qquad \mathbb{E}\bigl[2 L_2 + L_1^2\bigr] = m (m + 2)\, n (n + 2)\, \sigma^4.$$

By the Cauchy–Schwarz inequality $m L_2 \ge L_1^2$, with equality exactly when all eigenvalues are equal, that is,
when $X$ is a scalar matrix. For $m = 1$ this always holds, so $m L_2 - L_1^2 = 0$; if $\sigma^2 = 0$ then
$M = 0$ and $m L_2 - L_1^2 = 0$ surely. If $\sigma^2 > 0$, $m \ge 2$ and $n \ge 1$, then
$m L_2 - L_1^2 > 0$ almost surely. On the event $m L_2 > L_1^2$, the method-of-moments estimators

$$\hat n = \frac{(m + 2) L_1^2}{m L_2 - L_1^2}, \qquad \hat\sigma^2 = \frac{L_1}{m \hat n}$$

are the unique solution $(\hat n, \hat\sigma^2)$ with $\hat n > 0$ of the two moment equations

$$L_1 = m \hat n \hat\sigma^2, \qquad 2 L_2 + L_1^2 = m (m + 2)\, \hat n (\hat n + 2)\, \hat\sigma^4.$$

## Proof depends on

- [The square of a standard normal variable is chi-square with one degree of freedom](../../../Probability/distributions/continuous/chi-square-distribution/gaussian-real-map-sq.md)

## Expansion

1. The entries of $X$ satisfy $\mathbb{E}[X_{ii}] = n\sigma^2$, $\mathbb{E}[X_{ii}^2] = n(n+2)\sigma^4$ and
   $\mathbb{E}[X_{ij}^2] = n\sigma^4$ for $i \ne j$; summing over the $m$ diagonal and $m(m-1)$ off-diagonal
   entries gives $\mathbb{E}[L_1]$ and $\mathbb{E}[L_2] = mn(n+2)\sigma^4 + m(m-1)n\sigma^4$.
2. For $\sigma^2 > 0$, $L_1 / \sigma^2$ is a sum of $mn$ independent $\chi_1^2$ variables, so $\mathbb{E}[L_1^2] = mn(mn+2)\sigma^4$,
   and $2\,\mathbb{E}[L_2] + \mathbb{E}[L_1^2] = mn\sigma^4(mn + 2m + 2n + 4)$; for $\sigma^2 = 0$ all three moments
   vanish, so the identities hold trivially.
3. For $m \ge 2$ the set of $M$ with $M M^\top$ scalar is a proper real algebraic subset of
   $\mathbb{R}^{m \times n}$ (its first two diagonal entries differ at some $M$), hence Lebesgue-null. For
   $\sigma^2 > 0$ the law of $M$ has a density with respect to Lebesgue measure, so this set has probability $0$;
   at $\sigma^2 = 0$ the law is the point mass at $0$, which lies in the set.
4. Substituting $\hat\sigma^2 = L_1/(m\hat n)$ into the second equation gives
   $2L_2 + L_1^2 = (m+2)(1 + 2/\hat n)L_1^2/m$, which is linear in $1/\hat n$ and solves to the stated $\hat n$.
   For eigenvalues $1$ and $3$ ($m = 2$), $\hat n = 16$.

## Sources

- N. Patterson, A. L. Price, and D. Reich, "Population Structure and Eigenanalysis", PLOS Genetics 2 (2006), e190, <https://doi.org/10.1371/journal.pgen.0020190> (PMC1713260). (Theorem 1 and Eqs. 23–26, which fit $L_1$ and $2L_2 + L_1^2$.)
