# Error of the composite Simpson rule

Let $a < b$, let $f$ have four continuous derivatives on $[a, b]$, let $n \ge 2$ be even, $h = (b - a)/n$ and $x_i = a + ih$. Then there is $\xi \in [a, b]$ such that

$$\int_a^b f(x)\, dx - \frac{h}{3}\Bigl(f(x_0) + 2\sum_{i=2}^{n/2} f(x_{2i-2}) + 4\sum_{i=1}^{n/2} f(x_{2i-1}) + f(x_n)\Bigr) = -\frac{(b - a)\, h^4}{180}\, f^{(4)}(\xi).$$

So the composite Simpson rule is fourth-order accurate. The proof applies the [error of Simpson's rule](simpson-rule-error.md) on each of the $n/2$ pairs of subintervals, of length $2h$, and replaces the average of the $f^{(4)}(\xi_i)$ by a value $f^{(4)}(\xi)$.

## Depends on

- [Quadrature rule](quadrature-rule.md)

## Proof depends on

- [Error of Simpson's rule](simpson-rule-error.md)

## Sources

- D. Levy, *Introduction to Numerical Analysis*, lecture notes, Department of Mathematics, University of Maryland, version of 4 January 2021, Section 6.5.2, the composite rule (6.25) and its error, the display before (6.26), which equals $-\tfrac{h^5}{90}\cdot\tfrac{n}{2} f^{(4)}(\xi) = -\tfrac{(b-a)h^4}{180} f^{(4)}(\xi)$ since $nh = b - a$; the final display (6.26) omits the factor $b - a$. <https://www.math.umd.edu/~dlevy/resources/notes.pdf>
