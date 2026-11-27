# Differentiation of the interpolating polynomial

Let $n \ge 1$, let $x_0, \dots, x_n$ be distinct points, let $I$ be the smallest closed interval containing them, let $f$ be $n + 2$ times continuously differentiable on $I$, and let $Q_n$ be the polynomial of degree at most $n$ interpolating $f$ at the nodes, with Lagrange basis polynomials $l_0, \dots, l_n$. Then for each node $x_k$ there is $\xi_k \in I$ with

$$f'(x_k) = \sum_{j=0}^n f(x_j)\, l_j'(x_k) + \frac{f^{(n+1)}(\xi_k)}{(n + 1)!} \prod_{j \ne k} (x_k - x_j).$$

The sum is $Q_n'(x_k)$, a differentiation formula for $f'(x_k)$ from the values $f(x_0), \dots, f(x_n)$.

## Depends on

- [Lagrange interpolation](../../approximation-theory/lagrange-interpolation/eval-interpolant.md)

## Proof depends on

- [Error of polynomial interpolation](../polynomial-and-spline-interpolation/interpolation-error-formula.md)

## Sources

- D. Levy, *Introduction to Numerical Analysis*, lecture notes, Department of Mathematics, University of Maryland, version of 4 January 2021, Section 5.2, formulas (5.7)–(5.10). The derivation differentiates the error term $f^{(n+1)}(\xi_x) w(x)/(n+1)!$; at a node the term containing the derivative of $\xi_x$ is multiplied by $w(x_k) = 0$, and the smoothness assumed here makes $x \mapsto f^{(n+1)}(\xi_x)$ differentiable, since it equals $(n+1)!\, f[x_0, \dots, x_n, x]$. <https://www.math.umd.edu/~dlevy/resources/notes.pdf>
