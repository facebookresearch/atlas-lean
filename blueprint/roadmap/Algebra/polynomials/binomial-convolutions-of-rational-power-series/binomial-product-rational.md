# Binomial products of proper rational series

Let $K$ be a field of characteristic $0$, let
$\alpha_1, \dots, \alpha_m, \beta_1, \dots, \beta_n \in K$, not necessarily distinct or nonzero,
and let $R$, $S$ be polynomials over $K$ with $\deg R < m$ and $\deg S < n$. If $A$, $B$ are power
series over $K$ with $A(x) \prod_{i=1}^m (1 - \alpha_i x) = R(x)$ and
$B(x) \prod_{j=1}^n (1 - \beta_j x) = S(x)$, then there is a polynomial $T$ over $K$ with
$\deg T < mn$ such that

$$(A \odot B)(x) \prod_{i=1}^m \prod_{j=1}^n \bigl(1 - (\alpha_i + \beta_j) x\bigr) = T(x),$$

where $\odot$ is the binomial product.

Here $\deg 0 = -\infty$, so $T = 0$ when $mn = 0$.

## Sources

- Ira M. Gessel and Ishan Kar, *Binomial Convolutions for Rational Power Series*, Journal of Integer Sequences 27 (2024), Article 24.1.3, Theorem 6 (`jis-2024-24.1.3-thm-6`).
