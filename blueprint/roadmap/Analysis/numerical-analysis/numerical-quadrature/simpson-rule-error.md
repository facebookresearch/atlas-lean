# Error of Simpson's rule

Let $a < b$ and let $f$ have four continuous derivatives on $[a, b]$. Then there is $\xi \in (a, b)$ such that

$$\int_a^b f(x)\, dx - \frac{b - a}{6}\Bigl(f(a) + 4 f\Bigl(\frac{a + b}{2}\Bigr) + f(b)\Bigr) = -\frac{1}{90} \Bigl(\frac{b - a}{2}\Bigr)^5 f^{(4)}(\xi).$$

In particular Simpson's rule, although built from the quadratic interpolant at three nodes, is exact for polynomials of degree at most $3$. With $c = (a + b)/2$, let $p_3$ be the cubic with $p_3 = f$ at $a, c, b$ and $p_3'(c) = f'(c)$. It differs from the quadratic interpolant at $a, c, b$ by a multiple of $(x - a)(x - c)(x - b)$, whose integral over $[a, b]$ vanishes, so Simpson's rule is $\int_a^b p_3$. As in the [error of polynomial interpolation](../polynomial-and-spline-interpolation/interpolation-error-formula.md), applying Rolle's theorem to $f - p_3 - \lambda (y - a)(y - c)^2 (y - b)$, which has zeros at $a$, $b$, $x$ and a double zero at $c$, gives $f(x) - p_3(x) = \frac{f^{(4)}(\eta_x)}{24}(x - a)(x - c)^2(x - b)$; this factor has one sign on $[a, b]$, so the mean value theorem for integrals and $\int_a^b (x - a)(x - c)^2(x - b)\, dx = -\tfrac{4}{15}\bigl(\tfrac{b - a}{2}\bigr)^5$ give the formula.

## Depends on

- [Quadrature rule](quadrature-rule.md)

## Proof depends on

- [Error of polynomial interpolation](../polynomial-and-spline-interpolation/interpolation-error-formula.md)
- [Error of Hermite interpolation](../polynomial-and-spline-interpolation/hermite-interpolation-error.md)
- [Rolle's theorem](../../real-functions/differential-calculus/rolle-theorem.md)

## Sources

- D. Levy, *Introduction to Numerical Analysis*, lecture notes, Department of Mathematics, University of Maryland, version of 4 January 2021, Section 6.4.2, Simpson's quadrature (6.20), and Section 6.5.1, the error analysis (6.21)–(6.24). <https://www.math.umd.edu/~dlevy/resources/notes.pdf>
