# Double-sum formula for Euler polynomials

Let $E_n(x)$ denote the Euler polynomial and
$S(n, k, x) = \frac{1}{k!} \sum_{j=0}^{k} \binom{k}{j} (-1)^{k-j} (x + j)^n$ the generalized
Stirling polynomial. For every $n \ge 0$, as polynomials in $x$ with rational coefficients,
$2^n E_n(x) = \sum_{\ell=0}^{n} \frac{(-1)^\ell}{\ell + 1}
\sum_{k=0}^{n-\ell} \frac{(k + \ell + 1)!}{2^k} \binom{\ell + 1}{k} S(n, k + \ell, 2x - 1)$.

## Sources

- Nouara Mokhtari, Rachid Boumahdi, and Farid Bencherif, "Generalizations of Several Explicit Formulas for Euler Polynomials", Theorem 4.3.
