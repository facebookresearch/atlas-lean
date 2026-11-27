# Error of the one-sided difference quotient

Let $h \ne 0$ and let $f$ be twice continuously differentiable on the closed interval between $x$ and $x + h$. Then there is a point $\xi$ strictly between $x$ and $x + h$ with

$$f'(x) = \frac{f(x + h) - f(x)}{h} - \frac{h}{2} f''(\xi).$$

For $h > 0$ this is the forward difference, and with $h$ replaced by $-h$ the backward difference $f'(x) = (f(x) - f(x - h))/h + \frac{h}{2} f''(\xi)$; both are first-order approximations.

## Proof depends on

- [Taylor's theorem with the Lagrange remainder](../../real-functions/differential-calculus/taylor-theorem-with-lagrange-remainder.md)

## Sources

- D. Levy, *Introduction to Numerical Analysis*, lecture notes, Department of Mathematics, University of Maryland, version of 4 January 2021, Section 5.1, formula (5.3), and Section 5.2, Example 5.1 with the forward and backward differences derived from (5.11). <https://www.math.umd.edu/~dlevy/resources/notes.pdf>
