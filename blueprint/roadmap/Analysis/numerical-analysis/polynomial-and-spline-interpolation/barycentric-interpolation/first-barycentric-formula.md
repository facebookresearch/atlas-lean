# First barycentric formula

Let $x_0, \dots, x_n$ be distinct nodes with node polynomial $\ell$ and [barycentric weights](barycentric-weights.md) $w_j$, and let $p$ be the polynomial of degree at most $n$ with $p(x_j) = f_j$ for all $j$. Then for every $x$ that is not a node

$$p(x) = \ell(x) \sum_{j=0}^n \frac{w_j}{x - x_j}\, f_j .$$

This is the Lagrange formula with the common factor $\ell(x)$ taken out of the basis polynomials $\ell_j(x) = \ell(x)\, w_j/(x - x_j)$; it evaluates $p(x)$ in $O(n)$ operations once the weights are known.

## Depends on

- [Barycentric weights](barycentric-weights.md)
- [Lagrange interpolation](../../../approximation-theory/lagrange-interpolation/eval-interpolant.md)

## Sources

- J.-P. Berrut and L. N. Trefethen, "Barycentric Lagrange interpolation", *SIAM Review* 46(3):501–517, 2004, Section 3, the derivation of (3.3) from the Lagrange formula (2.1). <https://people.maths.ox.ac.uk/trefethen/barycentric.pdf>
