# Error of Simpson's rule

Let $a < b$ and let $f$ have four continuous derivatives on $[a, b]$. Then there is $\xi \in (a, b)$ such that

$$\int_a^b f(x)\, dx - \frac{b - a}{6}\Bigl(f(a) + 4 f\Bigl(\frac{a + b}{2}\Bigr) + f(b)\Bigr) = -\frac{1}{90} \Bigl(\frac{b - a}{2}\Bigr)^5 f^{(4)}(\xi).$$

In particular Simpson's rule, although built from the quadratic interpolant at three nodes, is exact for polynomials of degree at most $3$. The proof uses that $\int_a^b (x - a)(x - \tfrac{a+b}{2})(x - b)\, dx = 0$, so that adding the midpoint again as a node does not change the rule, and then applies the [error of polynomial interpolation](../polynomial-and-spline-interpolation/interpolation-error-formula.md) with the double node and the mean value theorem for integrals.

## Depends on

- [Quadrature rule](quadrature-rule.md)

## Proof depends on

- [Error of polynomial interpolation](../polynomial-and-spline-interpolation/interpolation-error-formula.md)
- [Error of Hermite interpolation](../polynomial-and-spline-interpolation/hermite-interpolation-error.md)

## Sources

- D. Levy, *Introduction to Numerical Analysis*, lecture notes, Department of Mathematics, University of Maryland, version of 4 January 2021, Section 6.4.2, Simpson's quadrature (6.20), and Section 6.5.1, the error analysis (6.21)–(6.24). <https://www.math.umd.edu/~dlevy/resources/notes.pdf>
