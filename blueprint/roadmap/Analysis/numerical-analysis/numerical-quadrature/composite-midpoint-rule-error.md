# Error of the composite midpoint rule

Let $a < b$, let $f$ have a continuous second derivative on $[a, b]$, let $n \ge 1$, $h = (b - a)/n$ and let $x_j = a + (j - \tfrac12) h$, $1 \le j \le n$, be the midpoints of the $n$ equal subintervals. Then there is $\xi \in (a, b)$ such that

$$\int_a^b f(x)\, dx - h \sum_{j=1}^{n} f(x_j) = \frac{(b - a)\, h^2}{24}\, f''(\xi).$$

So the composite midpoint rule is second-order accurate. The proof sums the [error of the midpoint rule](midpoint-rule-error.md) over the subintervals and replaces the average of $f''(\xi_j)$ by a value $f''(\xi)$, by the intermediate value theorem.

## Depends on

- [Quadrature rule](quadrature-rule.md)

## Proof depends on

- [Error of the midpoint rule](midpoint-rule-error.md)

## Sources

- D. Levy, *Introduction to Numerical Analysis*, lecture notes, Department of Mathematics, University of Maryland, version of 4 January 2021, Section 6.3, the composite midpoint rule (6.15) and its error (6.16). <https://www.math.umd.edu/~dlevy/resources/notes.pdf>
