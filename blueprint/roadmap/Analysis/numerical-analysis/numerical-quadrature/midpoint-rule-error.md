# Error of the midpoint rule

Let $a < b$ and let $f$ have a continuous second derivative on $[a, b]$. Then there is $\xi \in (a, b)$ such that

$$\int_a^b f(x)\, dx - (b - a)\, f\Bigl(\frac{a + b}{2}\Bigr) = \frac{(b - a)^3}{24}\, f''(\xi).$$

In particular the midpoint rule is exact for polynomials of degree at most $1$. The proof replaces $f$ by its tangent line at the midpoint $c$, whose integral is $(b - a) f(c)$, and bounds the remainder $\tfrac12 f''(\xi_x)(x - c)^2$ by the mean value theorem for integrals.

## Depends on

- [Quadrature rule](quadrature-rule.md)

## Sources

- D. Levy, *Introduction to Numerical Analysis*, lecture notes, Department of Mathematics, University of Maryland, version of 4 January 2021, Section 6.1, the midpoint rule (6.4) and the derivation of its error ending in (6.6). <https://www.math.umd.edu/~dlevy/resources/notes.pdf>
