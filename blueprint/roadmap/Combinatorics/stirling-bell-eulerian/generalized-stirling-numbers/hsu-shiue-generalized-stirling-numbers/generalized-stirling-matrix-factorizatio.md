# Factorization of the generalized Stirling matrix

Let $S$ assign to real numbers $a, b, c$
and natural numbers $n, k$ a real number $S(a, b, c; n, k)$, such that for all real $a, b, c, x$
and every natural number $n$

$$\prod_{i=0}^{n-1} (x - i a) =
\sum_{k=0}^{n} S(a, b, c; n, k) \prod_{i=0}^{k-1} (x - c - i b),$$

and $S(a, b, c; n, k) = 0$ whenever $n < k$. Then for all real $\alpha, \beta, \gamma$ and all
natural numbers $n, k$

$$S(\alpha, \beta, \gamma; n, k) = \sum_{j=0}^{n} \sum_{l=0}^{j}
S(\alpha, 0, 0; n, j)\, S(0, 0, \gamma; j, l)\, S(0, \beta, 0; l, k).$$

In matrix form, the generalized Stirling matrix with parameters $(\alpha, \beta, \gamma)$ is the
product of the matrices for $(\alpha, 0, 0)$ (first kind), $(0, 0, \gamma)$ (translation) and
$(0, \beta, 0)$ (second kind).

## Sources

- Jiaqiang Pan, “Matrix Decomposition of the Unified Generalized Stirling Numbers and Inversion of the Generalized Factorial Matrices,” Journal of Integer Sequences 15 (2012), Article 12.6.6, Theorem `t:Decomposition`, lines 250-256, <https://cs.uwaterloo.ca/journals/JIS/VOL15/Pan/pan19.tex>.
