# Divided differences and derivatives

Let $x, x_0, \dots, x_{n-1}$ be $n + 1$ distinct real numbers, $n \ge 1$, let $a$ and $b$ be the smallest and the largest of them, and let $f$ have $n$ continuous derivatives on $[a, b]$. Then there is $\xi \in (a, b)$ such that the [divided difference](divided-differences.md) satisfies

$$f[x_0, \dots, x_{n-1}, x] = \frac{f^{(n)}(\xi)}{n!}.$$

For $n = 1$ this is the mean value theorem. Comparing the [Newton form](newton-form-of-the-interpolating-polynomial.md) of the interpolant at $x_0, \dots, x_{n-1}, x$, evaluated at $x$, with the [interpolation error formula](interpolation-error-formula.md) for the interpolant at $x_0, \dots, x_{n-1}$ gives the result.

## Depends on

- [Divided differences](divided-differences.md)

## Proof depends on

- [Newton form of the interpolating polynomial](newton-form-of-the-interpolating-polynomial.md)
- [Error of polynomial interpolation](interpolation-error-formula.md)

## Sources

- D. Levy, *Introduction to Numerical Analysis*, lecture notes, Department of Mathematics, University of Maryland, version of 4 January 2021, Section 3.7, Lemma 3.10 and its proof, which applies Theorem 3.9 and so uses an $n$-times continuously differentiable $f$ on $[a, b]$; the statement of the lemma asks for continuity of $f^{(n)}$ on $(a, b)$. <https://www.math.umd.edu/~dlevy/resources/notes.pdf>
