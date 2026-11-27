# Differentiation of the interpolating polynomial

Let $n \ge 1$, let $x_0, \dots, x_n$ be distinct points, let $I$ be the smallest closed interval containing them, let $f$ be $n + 1$ times continuously differentiable on $I$, and let $Q_n$ be the polynomial of degree at most $n$ interpolating $f$ at the nodes, with Lagrange basis polynomials $l_0, \dots, l_n$. Then for each node $x_k$ there is $\xi_k$ in the interior of $I$ with

$$f'(x_k) = \sum_{j=0}^n f(x_j)\, l_j'(x_k) + \frac{f^{(n+1)}(\xi_k)}{(n + 1)!} \prod_{j \ne k} (x_k - x_j).$$

The sum is $Q_n'(x_k)$, a differentiation formula for $f'(x_k)$ from the values $f(x_0), \dots, f(x_n)$. Proof: let $w(t) = \prod_j (t - x_j)$, so $w'(x_k) = \prod_{j \ne k}(x_k - x_j) \ne 0$, let $c = (f'(x_k) - Q_n'(x_k))/w'(x_k)$ and $g = f - Q_n - cw$. Then $g$ vanishes at the $n + 1$ nodes and $g'(x_k) = 0$. By [Rolle's theorem](../../real-functions/differential-calculus/rolle-theorem.md) $g'$ has a zero in each of the $n$ open gaps between consecutive nodes, which with $x_k$ gives $n + 1$ distinct zeros in $I$, also when $x_k$ is an endpoint; applying Rolle's theorem $n$ more times gives a zero $\xi_k$ of $g^{(n+1)} = f^{(n+1)} - (n+1)!\,c$ in the interior of $I$.

## Depends on

- [Lagrange interpolation](../../approximation-theory/lagrange-interpolation/eval-interpolant.md)
- [Evaluated Lagrange basis polynomial](../../approximation-theory/lagrange-interpolation/eval-basis.md)

## Proof depends on

- [Rolle's theorem](../../real-functions/differential-calculus/rolle-theorem.md)

## Related topics

- [Error of polynomial interpolation](../polynomial-and-spline-interpolation/interpolation-error-formula.md)

## Sources

- D. Levy, *Introduction to Numerical Analysis*, lecture notes, Department of Mathematics, University of Maryland, version of 4 January 2021, Section 3.7, Theorem 3.9, and Section 5.2, formulas (5.7)–(5.10), under $n + 1$ continuous derivatives with the remainder point between the extreme nodes; the Rolle argument above avoids differentiating the remainder point. <https://www.math.umd.edu/~dlevy/resources/notes.pdf>
