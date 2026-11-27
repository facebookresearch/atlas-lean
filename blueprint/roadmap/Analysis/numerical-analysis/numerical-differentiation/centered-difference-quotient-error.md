# Error of the centered difference quotient

Let $h > 0$ and let $f$ be three times continuously differentiable on $[x - h, x + h]$. Then there is $\xi \in (x - h, x + h)$ with

$$f'(x) = \frac{f(x + h) - f(x - h)}{2h} - \frac{h^2}{6} f'''(\xi),$$

so the centered difference quotient is a second-order approximation of $f'(x)$.

## Proof depends on

- [Taylor's theorem with the Lagrange remainder](../../real-functions/differential-calculus/taylor-theorem-with-lagrange-remainder.md)
- [Intermediate value theorem](../../real-functions/continuity-and-functional-equations/intermediate-value-theorem.md)

## Sources

- D. Levy, *Introduction to Numerical Analysis*, lecture notes, Department of Mathematics, University of Maryland, version of 4 January 2021, Section 5.1, formulas (5.4)–(5.5) and the Taylor expansion argument with the intermediate value theorem before (5.5); Section 5.2, Example 5.3. <https://www.math.umd.edu/~dlevy/resources/notes.pdf>
