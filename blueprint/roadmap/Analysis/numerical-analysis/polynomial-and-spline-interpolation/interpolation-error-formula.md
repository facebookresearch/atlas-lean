# Error of polynomial interpolation

Let $a < b$, let $f$ have $n + 1$ continuous derivatives on $[a, b]$, and let $Q_n$ be the polynomial of degree at most $n$ that interpolates $f$ at $n + 1$ distinct points $x_0, \dots, x_n \in [a, b]$. Then for every $x \in [a, b]$ there is $\xi \in (a, b)$ such that

$$f(x) - Q_n(x) = \frac{f^{(n+1)}(\xi)}{(n+1)!} \prod_{j=0}^{n} (x - x_j).$$

For $x$ not a node, the function $F(y) = f(y) - Q_n(y) - \lambda \prod_j (y - x_j)$, with $\lambda$ chosen so that $F(x) = 0$, has $n + 2$ zeros in $[a, b]$, and Rolle's theorem applied $n + 1$ times gives a zero $\xi$ of $F^{(n+1)}$.

## Depends on

- [Lagrange interpolant](../../approximation-theory/lagrange-interpolation/eval-interpolant.md)

## Proof depends on

- [Rolle's theorem](../../real-functions/differential-calculus/rolle-theorem.md)

## Sources

- D. Levy, *Introduction to Numerical Analysis*, lecture notes, Department of Mathematics, University of Maryland, version of 4 January 2021, Section 3.7, Theorem 3.9 and its proof. <https://www.math.umd.edu/~dlevy/resources/notes.pdf>
