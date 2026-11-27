# Richardson extrapolation of the centered difference quotient

Let $f$ be five times continuously differentiable on $[x - 2h_0, x + 2h_0]$, and for $0 < h \le h_0$ let $D(h) = (f(x + h) - f(x - h))/(2h)$. Then there is a constant $C$ such that for $0 < h \le h_0$

$$\Big| f'(x) - \frac{4D(h) - D(2h)}{3} \Big| \le C h^4, \qquad \frac{4D(h) - D(2h)}{3} = \frac{-f(x + 2h) + 8f(x + h) - 8f(x - h) + f(x - 2h)}{12h} .$$

By Taylor's theorem to order five, the combination cancels the $h^2$ term of the error expansion $f'(x) = D(h) - \frac{h^2}{6} f'''(x) + O(h^4)$; repeating the step with more smoothness cancels the $h^4$ term, giving $(16 S(h) - S(2h))/15$ for the five-point formula $S(h)$.

## Related topics

- [Error of the centered difference quotient](centered-difference-quotient-error.md): the $h^2$ remainder under three continuous derivatives.

## Sources

- D. Levy, *Introduction to Numerical Analysis*, lecture notes, Department of Mathematics, University of Maryland, version of 4 January 2021, Section 5.4, formulas (5.18)–(5.23). <https://www.math.umd.edu/~dlevy/resources/notes.pdf>
