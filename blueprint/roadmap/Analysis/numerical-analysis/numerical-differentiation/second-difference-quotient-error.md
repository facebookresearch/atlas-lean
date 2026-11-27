# Error of the second difference quotient

Let $h > 0$ and let $f$ be four times continuously differentiable on $[x - h, x + h]$. Then there is $\xi \in (x - h, x + h)$ with

$$\frac{f(x + h) - 2f(x) + f(x - h)}{h^2} = f''(x) + \frac{h^2}{12} f^{(4)}(\xi),$$

so the second difference quotient is a second-order approximation of $f''(x)$.

## Proof depends on

- [Taylor's theorem with the Lagrange remainder](../../real-functions/differential-calculus/taylor-theorem-with-lagrange-remainder.md)
- [Intermediate value theorem](../../real-functions/continuity-and-functional-equations/intermediate-value-theorem.md)

## Sources

- D. Levy, *Introduction to Numerical Analysis*, lecture notes, Department of Mathematics, University of Maryland, version of 4 January 2021, Section 5.1, formula (5.6) and the Taylor expansion argument after it. <https://www.math.umd.edu/~dlevy/resources/notes.pdf>
