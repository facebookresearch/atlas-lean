# Binomial products of arbitrary rational series

Let $K$ be a field of characteristic $0$,
let $\alpha_1, \dots, \alpha_m$ and $\beta_1, \dots, \beta_n$ be nonzero elements of $K$, and let
$R$, $S$ be polynomials over $K$. Let $A$, $B$ be power series over $K$ with
$A(x) \prod_{i=1}^m (1 - \alpha_i x) = R(x)$ and $B(x) \prod_{j=1}^n (1 - \beta_j x) = S(x)$.
Put $u = \max(d_R + 1 - m, 0)$ and $v = \max(d_S + 1 - n, 0)$, where $d_R$ and $d_S$ are the
degrees of $R$ and $S$, the zero polynomial counting as degree $0$. Then there is a polynomial
$T$ over $K$ of degree less than $(u + m)(v + n)$ such that

$$(A \odot B)(x) \Big(\prod_{i=1}^m (1 - \alpha_i x)\Big)^{v}
\Big(\prod_{j=1}^n (1 - \beta_j x)\Big)^{u} \prod_{i=1}^m \prod_{j=1}^n (1 - (\alpha_i + \beta_j) x)
= T(x),$$

where $\odot$ is the binomial product.

## Sources

- Ira M. Gessel and Ishan Kar, *Binomial Convolutions for Rational Power Series*, Journal of Integer Sequences 27 (2024), Article 24.1.3, Corollary 7 (`jis-2024-24.1.3-cor-7`).
