# Second-order one-sided difference quotient

Let $h > 0$ and let $f$ be three times continuously differentiable on $[x, x + 2h]$. Then there is $\xi \in (x, x + 2h)$ with

$$f'(x) = \frac{-3f(x) + 4f(x + h) - f(x + 2h)}{2h} + \frac{h^2}{3} f'''(\xi).$$

It is the derivative at $x$ of the quadratic interpolant $Q$ of $f$ at $x$, $x + h$, $x + 2h$. Proof: let $w(t) = (t - x)(t - x - h)(t - x - 2h)$, so $w'(x) = 2h^2$, and choose $c$ with $f'(x) = Q'(x) + c\,w'(x)$. Then $g = f - Q - cw$ vanishes at the three nodes and $g'(x) = 0$, so by [Rolle's theorem](../../real-functions/differential-calculus/rolle-theorem.md) $g'$ has two further zeros in $(x, x + 2h)$, $g''$ has two zeros and $g'''$ one zero $\xi \in (x, x + 2h)$; thus $6c = f'''(\xi)$ and $c\,w'(x) = \tfrac{h^2}{3} f'''(\xi)$.

## Depends on

- [Lagrange interpolation](../../approximation-theory/lagrange-interpolation/eval-interpolant.md)

## Proof depends on

- [Rolle's theorem](../../real-functions/differential-calculus/rolle-theorem.md)

## Related topics

- [Differentiation of the interpolating polynomial](differentiation-of-the-interpolating-polynomial.md): the general node formula for $n + 1$ nodes, under $n + 1$ continuous derivatives, of which this page is the case $n = 2$ at the left endpoint.

## Sources

- D. Levy, *Introduction to Numerical Analysis*, lecture notes, Department of Mathematics, University of Maryland, version of 4 January 2021, Section 5.2, Example 5.2, formula (5.12) with $x_0 = x$, $x_1 = x + h$, $x_2 = x + 2h$. <https://www.math.umd.edu/~dlevy/resources/notes.pdf>
