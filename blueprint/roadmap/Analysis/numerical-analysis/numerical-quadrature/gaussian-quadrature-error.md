# Error of Gaussian quadrature

Let $w$ be a weight function on $[a, b]$, let $f$ have $2n + 2$ continuous derivatives on $[a, b]$, and let $x_0, \dots, x_n$ and $A_0, \dots, A_n$ be the nodes and weights of the [Gaussian quadrature](gaussian-quadrature.md) with $n + 1$ nodes for $w$. Then there is $\zeta \in (a, b)$ such that

$$\int_a^b f(x)\, w(x)\, dx - \sum_{i=0}^{n} A_i f(x_i) = \frac{f^{(2n+2)}(\zeta)}{(2n+2)!} \int_a^b \prod_{j=0}^{n} (x - x_j)^2\, w(x)\, dx.$$

The Gaussian quadrature is the integral of the Hermite interpolant of $f$ at the nodes, the terms with $f'(x_i)$ dropping out because the node polynomial is orthogonal to the Lagrange basis polynomials; the [error of Hermite interpolation](../polynomial-and-spline-interpolation/hermite-interpolation-error.md) and the mean value theorem for integrals give the formula.

## Depends on

- [Gaussian quadrature](gaussian-quadrature.md)

## Proof depends on

- [Error of Hermite interpolation](../polynomial-and-spline-interpolation/hermite-interpolation-error.md)
- [Gaussian quadrature is exact to degree 2n + 1](gaussian-quadrature-is-exact-to-degree-2n-plus-1.md)

## Sources

- D. Levy, *Introduction to Numerical Analysis*, lecture notes, Department of Mathematics, University of Maryland, version of 4 January 2021, Section 6.7.2, the derivation of the Gaussian quadrature from the Hermite interpolant (6.36)–(6.38), and Theorem 6.12 with its proof. <https://www.math.umd.edu/~dlevy/resources/notes.pdf>
