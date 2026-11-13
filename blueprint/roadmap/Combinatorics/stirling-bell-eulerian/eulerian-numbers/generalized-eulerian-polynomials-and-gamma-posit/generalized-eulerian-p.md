# Generalized Eulerian polynomials

For rational numbers $q, t, x, y$ and $n \ge 0$, the
generalized Eulerian polynomial $P_n(q, t; x, y)$ is $n!$ times the coefficient of $z^n$ in the
formal power series over $\mathbb{Q}$

$$\mathcal{P}(q, t; x, y; z) = \left(\frac{x - y}{x e^{yz} - y e^{xz}}\right)^q e^{(x + y) q t z},$$

where the $q$-th power is the binomial series $(1 + u)^q = \sum_{k \ge 0} \binom{q}{k} u^k$
applied to $u = \frac{x - y}{x e^{yz} - y e^{xz}} - 1$. When $x \ne y$ the quotient has constant
term $1$, so $u$ has constant term $0$; for $x = y$ the formula is degenerate and the value of
$P_n$ is a formal convention.

## Sources

- Pasquale Petrullo and Domenico Senato, *Generalized Eulerian Polynomials with a Nonnegative Gamma Vector*, Journal of Integer Sequences 27 (2024), Article 24.1.5, Equation (3).
