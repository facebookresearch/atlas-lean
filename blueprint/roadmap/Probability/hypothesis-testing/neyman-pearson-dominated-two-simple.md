# Neyman–Pearson lemma

Let $\mu$ be a measure on a measurable space $\Omega$, and let
$p, q : \Omega \to \mathbb{R}$ be measurable, nonnegative and $\mu$-integrable. Let $k \ge 0$ be a
real number and let $\varphi^\star : \Omega \to [0, 1]$ be measurable with $\varphi^\star(x) = 1$
whenever $q(x) > k\,p(x)$ and $\varphi^\star(x) = 0$ whenever $q(x) < k\,p(x)$. Then every
measurable test $\varphi : \Omega \to [0, 1]$ satisfying
$\int \varphi\, p \, d\mu \le \int \varphi^\star p \, d\mu$ also satisfies
$\int \varphi\, q \, d\mu \le \int \varphi^\star q \, d\mu$.

No normalization of $p$ or $q$ and no condition on $\varphi^\star$ on the set where $q = k\,p$ are
assumed.

## Sources

- J. Neyman and E. S. Pearson, "On the problem of the most efficient tests of statistical hypotheses", Phil. Trans. R. Soc. Lond. A 231 (1933), 289–337, DOI `10.1098/rsta.1933.0009`.
