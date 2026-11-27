# Gaussian quadrature

Let $w$ be a weight function on $[a, b]$ and $n \ge 0$. The *Gaussian quadrature* with $n + 1$ nodes for the weight $w$ is the [quadrature rule](quadrature-rule.md)

$$\int_a^b f(x)\, w(x)\, dx \approx \sum_{i=0}^{n} A_i f(x_i)$$

whose nodes $x_0, \dots, x_n$ are the zeros of a nonzero polynomial of degree $n + 1$ that is [$w$-orthogonal](orthogonal-polynomial-for-a-weight.md) to the polynomials of degree at most $n$, and whose weights are those of the [interpolatory rule](interpolatory-quadrature.md) on these nodes, $A_i = \int_a^b w(x) \prod_{j \ne i} \frac{x - x_j}{x_i - x_j}\, dx$. The nodes are distinct and lie in $(a, b)$ because of the [zeros of orthogonal polynomials](zeros-of-orthogonal-polynomials.md).

## Depends on

- [Quadrature rule](quadrature-rule.md)
- [Orthogonal polynomial for a weight](orthogonal-polynomial-for-a-weight.md)
- [Interpolatory quadrature rules](interpolatory-quadrature.md)
- [Zeros of orthogonal polynomials](zeros-of-orthogonal-polynomials.md)

## Sources

- D. Levy, *Introduction to Numerical Analysis*, lecture notes, Department of Mathematics, University of Maryland, version of 4 January 2021, Section 6.7.1, Theorem 6.7, the paragraph after it, and the definition of Gaussian quadrature at the end of Section 6.7.2 before Theorem 6.12. <https://www.math.umd.edu/~dlevy/resources/notes.pdf>
