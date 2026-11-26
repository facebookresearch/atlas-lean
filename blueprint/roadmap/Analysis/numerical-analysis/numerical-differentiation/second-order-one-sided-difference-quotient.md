# Second-order one-sided difference quotient

Let $h > 0$ and let $f$ be three times continuously differentiable on $[x, x + 2h]$. Then there is $\xi \in (x, x + 2h)$ with

$$f'(x) = \frac{-3f(x) + 4f(x + h) - f(x + 2h)}{2h} + \frac{h^2}{3} f'''(\xi).$$

It is the derivative at $x$ of the quadratic interpolant of $f$ at $x$, $x + h$, $x + 2h$.

## Proof depends on

- [Differentiation of the interpolating polynomial](differentiation-of-the-interpolating-polynomial.md)

## Sources

- D. Levy, *Introduction to Numerical Analysis*, lecture notes, Department of Mathematics, University of Maryland, version of 4 January 2021, Section 5.2, Example 5.2, formula (5.12) with $x_0 = x$, $x_1 = x + h$, $x_2 = x + 2h$. <https://www.math.umd.edu/~dlevy/resources/notes.pdf>
