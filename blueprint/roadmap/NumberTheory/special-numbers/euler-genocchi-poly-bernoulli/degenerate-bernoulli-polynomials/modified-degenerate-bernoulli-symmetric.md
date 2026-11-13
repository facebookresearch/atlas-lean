# Symmetric identity for modified degenerate Bernoulli polynomials

Let $m \ge 2$ and
$n \ge 1$ be integers, let $\lambda$ be a complex number with $\lambda \ne 0$ and $\lambda \ne -1$,
let $r_1, \ldots, r_m$ and $x_1, \ldots, x_m$ be complex numbers, write
$\mathfrak{B}_{k,\lambda}(x)$ for the modified degenerate Bernoulli polynomials, and put
$r_0 = n - r_1 - \cdots - r_m$. Then

$$
r_0 \sum_{k_1 + \cdots + k_m = n} \prod_{j=1}^{m} \binom{r_j}{k_j} \mathfrak{B}_{k_j,\lambda}(x_j)
= -\sum_{i=1}^{m} r_i \sum_{k_1 + \cdots + k_m = n} \binom{r_0}{k_i}
\mathfrak{B}_{k_i,\lambda}(1 - x_i)
\prod_{j \ne i} \binom{r_j}{k_j} \mathfrak{B}_{k_j,\lambda}(x_j - x_i + [j > i]),
$$

where $k_1, \ldots, k_m$ range over nonnegative integers, $\binom{w}{k} = w(w-1) \cdots
(w-k+1)/k!$ is the binomial coefficient with a complex upper argument, and $[j > i]$ is $1$ if
$j > i$ and $0$ otherwise.

## Sources

- Qi-Peng Su and Hao Pan, *Symmetric Identities on Modified Degenerate Bernoulli Polynomials*, Journal of Integer Sequences 27 (2024), Article 24.5.4, Theorem 1 (`jis-2024-24.5.4-thm-1`).
