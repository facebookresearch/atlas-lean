# Karamata's integral theorem

Let $W : \mathbb{R} \to \mathbb{R}$ be nonincreasing, nonnegative and bounded, with $W(x) > 0$ for
all sufficiently large $x$, and suppose that for some $\rho < 0$

$$\frac{W(cx)}{W(x)} \to c^{\rho} \qquad (x \to \infty) \quad \text{for every } c > 0 .$$

Let $\beta \ge 0$ with $\beta + 1 + \rho > 0$. Then

$$\frac{\int_0^x t^{\beta}\, W(t)\, dt}{x^{\beta + 1}\, W(x)} \to \frac{1}{\beta + 1 + \rho} \qquad (x \to \infty).$$

The proof substitutes $t = xu$ and applies dominated convergence, with [Potter's
bound](potter-upper.md) as the dominating function.

## Sources

- N. H. Bingham, C. M. Goldie and J. L. Teugels, *Regular Variation*, Cambridge University
  Press, 1987, Theorem 1.5.11 (direct half).
