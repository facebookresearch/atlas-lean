# Chebyshev interpolants are near-best

For $n \ge 1$, if a polynomial $q$ of degree at most $n$ satisfies $|f - q| \le E$ on
$[-1, 1]$, then the Chebyshev interpolant satisfies $|f - p_n| \le (2 + \frac{2}{\pi}\log(n + 1))E$
there. Taking $q$ the best approximation, Chebyshev interpolation loses at most a logarithmic
factor against the best possible polynomial.

## Informally uses

- [Lebesgue constants of Chebyshev points](sum-abs-lagrange-basis-chebyshev-le.md): the Lebesgue constant bound.

## Sources

- L. N. Trefethen, Approximation Theory and Approximation Practice, SIAM (2013; extended edition 2019), Theorem 16.1.
