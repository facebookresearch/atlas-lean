# A convolution lemma for modified degenerate Bernoulli polynomials

Let $m \ge 2$, let
$\lambda$ be a complex number with $\lambda \ne 0$ and $\lambda \ne -1$, let $s_1, \ldots, s_m$ be
nonnegative integers with $S = s_1 + \cdots + s_m$, and let $x_1, \ldots, x_m$ be complex numbers.
Writing $\mathfrak{B}_{n,\lambda}(x)$ for the modified degenerate Bernoulli polynomials,

$$
\sum_{i=1}^{m} s_i\, \mathfrak{B}_{s_i-1,\lambda}(x_i)
\prod_{j \ne i} \mathfrak{B}_{s_j,\lambda}(x_j) =
\sum_{i=1}^{m} s_i \sum_{k_1 + \cdots + k_m = S} \mathfrak{B}_{k_i-1,\lambda}(x_i)
\prod_{j \ne i} \binom{s_j}{k_j} \mathfrak{B}_{k_j,\lambda}(x_j - x_i + [j > i]),
$$

where $k_1, \ldots, k_m$ range over nonnegative integers, $[j > i]$ is $1$ if $j > i$ and $0$
otherwise, and $\mathfrak{B}_{-1,\lambda}$ is read as $0$ (on the left this term has the factor
$s_i = 0$).

## Sources

- Qi-Peng Su and Hao Pan, *Symmetric Identities on Modified Degenerate Bernoulli Polynomials*, Journal of Integer Sequences 27 (2024), Article 24.5.4, Lemma 3 (`jis-2024-24.5.4-lem-3`).
