# Error of Hermite interpolation

Let $a < b$, let $x_0, \dots, x_n$ be distinct points of $[a, b]$, and let $f$ have $2n + 2$ continuous derivatives on $[a, b]$. If $p$ is a polynomial of degree at most $2n + 1$ with

$$p(x_i) = f(x_i), \qquad p'(x_i) = f'(x_i), \qquad 0 \le i \le n,$$

then for every $x \in [a, b]$ there is $\xi \in (a, b)$ such that

$$f(x) - p(x) = \frac{f^{(2n+2)}(\xi)}{(2n+2)!} \prod_{i=0}^{n} (x - x_i)^2.$$

Such a $p$ exists and is unique; in Lagrange form $p(x) = \sum_i f(x_i)\bigl[1 + 2\ell_i'(x_i)(x_i - x)\bigr]\ell_i(x)^2 + \sum_i f'(x_i)(x - x_i)\ell_i(x)^2$ with the Lagrange basis polynomials $\ell_i$. The proof follows that of the [error of polynomial interpolation](interpolation-error-formula.md), with $\prod_i (y - x_i)^2$ in place of $\prod_i (y - x_i)$.

## Depends on

- [Evaluated Lagrange basis polynomial](../../approximation-theory/lagrange-interpolation/eval-basis.md)

## Proof depends on

- [Rolle's theorem](../../real-functions/differential-calculus/rolle-theorem.md)
- [Error of polynomial interpolation](interpolation-error-formula.md)

## Sources

- D. Levy, *Introduction to Numerical Analysis*, lecture notes, Department of Mathematics, University of Maryland, version of 4 January 2021, Section 3.9.2, the Lagrange form (3.50), and Theorem 3.20 with its proof. <https://www.math.umd.edu/~dlevy/resources/notes.pdf>
