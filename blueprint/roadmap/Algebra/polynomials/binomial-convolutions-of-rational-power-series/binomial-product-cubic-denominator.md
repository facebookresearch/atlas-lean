# Binomial products of series with a cubic denominator

Let $K$ be a field of characteristic
$0$, let $A, B, C \in K$ with $C \ne 0$, and let $D(x) = 1 + Ax + Bx^2 + Cx^3$. Suppose that
$D(x) = \prod_{i=1}^{3} (1 - \alpha_i x)$ with $\alpha_1, \alpha_2, \alpha_3 \in K$ and that
$2\alpha_i \ne \alpha_j + \alpha_k$ whenever $i, j, k \in \{1, 2, 3\}$ are not all equal. Let $r$
and $s$ be power series over $K$ such that $r D$ and $s D$ are polynomials of degree less than $3$.
Then there are polynomials $u$, $v$ over $K$ of degree at most $2$ such that

$$r \odot s = \frac{u(x)}{D(2x)} + \frac{1}{1 + Ax} \odot \frac{v(x)}{D(-x)},$$

where $\odot$ is the binomial product.

The second term uses the factor $1/(1 + Ax)$; with $1/(1 - Ax)$ in its place the statement already
fails for the tribonacci series $x/(1 - x - x^2 - x^3)$, where $A = -1$.

## Sources

- Ira M. Gessel and Ishan Kar, *Binomial Convolutions for Rational Power Series*, Journal of Integer Sequences 27 (2024), Article 24.1.3, Theorem 12 (`jis-2024-24.1.3-thm-12`).
