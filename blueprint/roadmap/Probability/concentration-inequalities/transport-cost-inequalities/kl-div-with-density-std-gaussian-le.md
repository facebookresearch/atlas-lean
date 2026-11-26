# Gross' logarithmic Sobolev inequality

Let $\gamma$ be the standard Gaussian measure on $\mathbb{R}^n$ (or on any finite-dimensional real
inner product space). For every smooth ($C^\infty$) positive $f$ with $\int f \, d\gamma = 1$,

$$\int f \log f \, d\gamma \le \frac12 \int \frac{|\nabla f|^2}{f} \, d\gamma ,$$

the left side being the relative entropy $\operatorname{KL}(f\gamma \,\|\, \gamma)$. The constant
does not depend on the dimension. Ledoux presents the proof of Bakry and Émery: interpolate the
entropy along the heat semigroup and use the commutation $\nabla P_u f = P_u \nabla f$ with the
Jensen and Cauchy–Schwarz inequalities.

This is the [logarithmic Sobolev inequality](satisfies-log-sobolev.md) with constant $\alpha = 1$,
stated for smooth positive densities as in the source rather than for nonnegative Lipschitz ones.
Through the [Otto–Villani theorem](satisfies-talagrand-of-satisfies-log-sob.md) it is the
log-Sobolev side of [Talagrand's inequality for the Gaussian measure](../talagrand-std-gaussian.md).

## Sources

- M. Ledoux, *Heat flows, geometric and functional inequalities*, Proceedings of the International Congress of Mathematicians, Seoul 2014, Theorem 2.1.
- L. Gross, *Logarithmic Sobolev inequalities*, Amer. J. Math. 97 (1975).
