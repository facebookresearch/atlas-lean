# Resultant identity for pairwise products

Let $K$ be a field of characteristic $0$, let
$m, n \ge 0$ be integers, and let $\alpha_1, \dots, \alpha_m$ and $\beta_1, \dots, \beta_n$ be
elements of $K$. Regard $f(y) = \prod_{i=1}^{m} (1 - \alpha_i y)$ and
$g(y) = \prod_{j=1}^{n} (y - \beta_j x)$ as polynomials in $y$ with coefficients in $K[x]$,
and let $\operatorname{Res}_{m,n}(f, g)$ be the determinant of their Sylvester matrix formed with
the formal degrees $m$ and $n$. Then in $K[x]$

$$
\prod_{i=1}^{m} \prod_{j=1}^{n} (1 - \alpha_i \beta_j x) = (-1)^{mn} \operatorname{Res}_{m,n}(f, g).
$$

With $U(x) = \prod_{i=1}^{m} (1 - \alpha_i x)$ and $V(x) = \prod_{j=1}^{n} (1 - \beta_j x)$, these
are $f(y) = U(y)$ and $g(y) = y^n V(x / y)$, the form used in the source.

## Sources

- Ira M. Gessel and Ishan Kar, *Binomial Convolutions for Rational Power Series*, Journal of Integer Sequences 27 (2024), Article 24.1.3, Theorem 14 (`jis-2024-24.1.3-thm-14`).
