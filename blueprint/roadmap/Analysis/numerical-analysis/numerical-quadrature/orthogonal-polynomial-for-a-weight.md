# Orthogonal polynomial for a weight

Let $w$ be a [weight function](quadrature-rule.md) on $[a, b]$ and $n \ge 0$. A polynomial $q$ is *$w$-orthogonal to the polynomials of degree at most $n$* if

$$\int_a^b p(x)\, q(x)\, w(x)\, dx = 0 \qquad \text{for every real polynomial } p \text{ of degree at most } n.$$

For every $n$ there is a nonzero such polynomial $q$ of degree exactly $n + 1$: the Gram–Schmidt orthogonalization of $1, x, x^2, \dots$ in the inner product $\langle f, g \rangle = \int_a^b f g w$ produces one for every degree. For $w \equiv 1$ on $[-1, 1]$ these are the Legendre polynomials, such as $P_2(x) = \tfrac12(3x^2 - 1)$.

## Depends on

- [Quadrature rule](quadrature-rule.md)

## Sources

- D. Levy, *Introduction to Numerical Analysis*, lecture notes, Department of Mathematics, University of Maryland, version of 4 January 2021, Section 4.3.5 (orthogonal polynomials with respect to a weight, constructed by Gram–Schmidt), Section 4.4, and Section 6.7.1, Theorem 6.7 and Example 6.10. <https://www.math.umd.edu/~dlevy/resources/notes.pdf>
