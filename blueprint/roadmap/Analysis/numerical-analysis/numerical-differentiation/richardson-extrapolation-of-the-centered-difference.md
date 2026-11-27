# Richardson extrapolation of the centered difference quotient

Let $f$ be five times continuously differentiable on $[x - 2h_0, x + 2h_0]$, and for $0 < t \le 2h_0$ let $D(t) = (f(x + t) - f(x - t))/(2t)$. Then there is a constant $C$ such that for $0 < h \le h_0$

$$\Big| f'(x) - \frac{4D(h) - D(2h)}{3} \Big| \le C h^4, \qquad \frac{4D(h) - D(2h)}{3} = \frac{-f(x + 2h) + 8f(x + h) - 8f(x - h) + f(x - 2h)}{12h} .$$

By Taylor's theorem to order five, the combination cancels the $h^2$ term of the error expansion $f'(x) = D(h) - \frac{h^2}{6} f'''(x) + O(h^4)$; repeating the step cancels the $h^4$ term: if $f$ is seven times continuously differentiable on the same interval and $S(t) = (4D(t) - D(2t))/3$ for $0 < t \le h_0$, then $(16 S(h) - S(2h))/15$ approximates $f'(x)$ with error $O(h^6)$ for $0 < h \le h_0/2$, where its samples $f(x \pm 4h)$ lie in the interval.

## Related topics

- [Error of the centered difference quotient](centered-difference-quotient-error.md): the $h^2$ remainder under three continuous derivatives.

## Sources

- D. Levy, *Introduction to Numerical Analysis*, lecture notes, Department of Mathematics, University of Maryland, version of 4 January 2021, Section 5.4, formulas (5.18)–(5.23). <https://www.math.umd.edu/~dlevy/resources/notes.pdf>
