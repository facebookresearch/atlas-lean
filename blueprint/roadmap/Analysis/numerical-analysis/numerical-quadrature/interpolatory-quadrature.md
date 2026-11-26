# Interpolatory quadrature rules

Let $w$ be a weight function on $[a, b]$ and let $x_0, \dots, x_n \in [a, b]$ be distinct. A [quadrature rule](quadrature-rule.md) $\int_a^b f(x) w(x)\, dx \approx \sum_{i=0}^{n} A_i f(x_i)$ with these nodes is exact on the polynomials of degree at most $n$ if and only if

$$A_i = \int_a^b w(x) \prod_{j \ne i} \frac{x - x_j}{x_i - x_j}\, dx, \qquad 0 \le i \le n,$$

that is, if and only if it integrates the Lagrange interpolant of $f$ at the nodes exactly. With $w \equiv 1$ and equally spaced nodes these are the Newton–Cotes rules: the trapezoidal rule $(b - a)\bigl(f(a) + f(b)\bigr)/2$ and Simpson's rule $\tfrac{b - a}{6}\bigl(f(a) + 4f(\tfrac{a+b}{2}) + f(b)\bigr)$.

## Depends on

- [Quadrature rule](quadrature-rule.md)
- [Lagrange interpolant](../../approximation-theory/lagrange-interpolation/eval-interpolant.md)

## Sources

- D. Levy, *Introduction to Numerical Analysis*, lecture notes, Department of Mathematics, University of Maryland, version of 4 January 2021, Section 6.2, (6.7)–(6.10) and items 1 and 2 after (6.11) (for $w \equiv 1$), Section 6.6, (6.28)–(6.29), and Section 6.7.1, the equivalence stated with (6.31)–(6.32). <https://www.math.umd.edu/~dlevy/resources/notes.pdf>
