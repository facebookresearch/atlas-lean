# Lebesgue constants of equispaced points grow exponentially

For the $n + 1$ equispaced nodes $x_j = a + j(b - a)/n$ on $[a, b]$, the Lebesgue constant satisfies

$$\Lambda_n \ge \frac{1}{2n^2}\binom{n}{\lfloor n/2 \rfloor},$$

which grows like $2^n/n^{5/2}$. So polynomial interpolation in equispaced points is exponentially ill-conditioned, the source of the Runge phenomenon.

## Proof depends on

- [The Lebesgue constant is bounded below by the ratio of the barycentric weights](lebesgue-constant-bounded-below-by-the-weight-ratio.md)
- [Barycentric weights for equispaced points](barycentric-weights-for-equispaced-points.md)

## Sources

- J.-P. Berrut and L. N. Trefethen, "Barycentric Lagrange interpolation", *SIAM Review* 46(3):501–517, 2004, Section 5, the equispaced weights (5.1) and the discussion of their exponential variation and the Runge phenomenon after it, and Section 9.1, the bound (9.2). <https://people.maths.ox.ac.uk/trefethen/barycentric.pdf>
