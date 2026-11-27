# Convergence of Gaussian quadrature

Let $w$ be a weight function on $[a, b]$ and $f$ a continuous function on $[a, b]$. For each $n$, let $\sum_{i=0}^{n} A_{n,i} f(x_{n,i})$ be the [Gaussian quadrature](gaussian-quadrature.md) with $n + 1$ nodes for $w$. Then

$$\lim_{n \to \infty} \sum_{i=0}^{n} A_{n,i} f(x_{n,i}) = \int_a^b f(x)\, w(x)\, dx.$$

The theorem gives no rate. Its standard proof approximates $f$ uniformly on $[a, b]$ by a polynomial $p$ within $\varepsilon$, which the Weierstrass theorem on $[0, 1]$ provides after the affine change of variable $x = a + (b - a)t$: the rule is exact for $p$ once $2n + 1 \ge \deg p$, and since its weights are positive with sum $\int_a^b w$, both the integral and the rule change by at most $\varepsilon \int_a^b w$ when $p$ is replaced by $f$.

## Depends on

- [Gaussian quadrature](gaussian-quadrature.md)

## Proof depends on

- [Gaussian quadrature is exact to degree 2n + 1](gaussian-quadrature-is-exact-to-degree-2n-plus-1.md)
- [The weights of Gaussian quadrature are positive](gaussian-quadrature-weights-are-positive.md)
- [Weierstrass approximation theorem on the unit interval](../../../Biology/population-genetics/diffusion-theory/wright-fisher-semigroup-and-moment-duality/dense-polynomial-functions.md)

## Sources

- D. Levy, *Introduction to Numerical Analysis*, lecture notes, Department of Mathematics, University of Maryland, version of 4 January 2021, Section 6.7.2, Theorem 6.13 and the paragraph before it, which refers to a proof based on the Weierstrass approximation theorem. <https://www.math.umd.edu/~dlevy/resources/notes.pdf>
