# Barycentric weights for equispaced points

For $n \ge 1$ and the equispaced nodes $x_j = a + j(b - a)/n$, $j = 0, \dots, n$, on an interval $[a, b]$ with $a < b$, the [barycentric weights](barycentric-weights.md) are a common factor times

$$w_j = (-1)^j \binom{n}{j},$$

so after the factor is dropped, which leaves the [second barycentric formula](second-barycentric-formula.md) unchanged, the weights do not depend on $a$ and $b$. Their ratio $\max_j |w_j| / \min_j |w_j| = \binom{n}{\lfloor n/2 \rfloor}$ is of order $2^n/\sqrt n$, reflecting the ill-conditioning of interpolation in equispaced points.

## Depends on

- [Barycentric weights](barycentric-weights.md)
- [Second barycentric formula](second-barycentric-formula.md)

## Sources

- J.-P. Berrut and L. N. Trefethen, "Barycentric Lagrange interpolation", *SIAM Review* 46(3):501–517, 2004, Section 5, the formula $w_j = (-1)^{n-j}\binom{n}{j}/(h^n n!)$ for spacing $h$, its simplification (5.1), and the discussion after it. <https://people.maths.ox.ac.uk/trefethen/barycentric.pdf>
