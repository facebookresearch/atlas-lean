# Barycentric weights for Chebyshev points

Let $n \ge 1$. On $[-1, 1]$, up to a common factor that cancels in the [second barycentric formula](second-barycentric-formula.md), the [barycentric weights](barycentric-weights.md) of the Chebyshev points are as follows.

- Chebyshev points of the first kind, $x_j = \cos\frac{(2j + 1)\pi}{2n + 2}$, $j = 0, \dots, n$: $\; w_j = (-1)^j \sin\frac{(2j + 1)\pi}{2n + 2}$.
- Chebyshev points of the second kind, $x_j = \cos\frac{j\pi}{n}$, $j = 0, \dots, n$: $\; w_j = (-1)^j \delta_j$, with $\delta_j = 1/2$ for $j = 0$ or $j = n$ and $\delta_j = 1$ otherwise.

The weights vary by factors at most $O(n)$, and an affine change of variable to $[a, b]$ with $a < b$ multiplies all of them by $2^n (b - a)^{-n}$.

## Depends on

- [Barycentric weights](barycentric-weights.md)
- [Second barycentric formula](second-barycentric-formula.md)

## Sources

- J.-P. Berrut and L. N. Trefethen, "Barycentric Lagrange interpolation", *SIAM Review* 46(3):501–517, 2004, Section 5, the identity (5.2), the formulas (5.3) (first kind) and (5.4) (second kind), and the remark on the interval $[a, b]$. <https://people.maths.ox.ac.uk/trefethen/barycentric.pdf>
