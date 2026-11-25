# Generating function of the generalized Eulerian polynomials

For rational numbers
$q$, $t$, $x$, $y$, this is the formal power series in $z$ over $\mathbb{Q}$

$$\mathcal{P}(q, t; x, y; z) = \left(\frac{x - y}{x e^{yz} - y e^{xz}}\right)^q e^{(x+y)qtz}.$$

Here the $q$-th power is the binomial series $(1 + u)^q = \sum_{n \ge 0} \binom{q}{n} u^n$
with $u$ the base minus $1$. For $x \ne y$ the base has constant term $1$, so $u$ has constant
term $0$. For $x = y$ the denominator is the zero series and the base is taken to be $0$ (the
inverse of the zero series being $0$), so $u = -1$: the series is then $1$ for $q = 0$ and $0$
for every positive integer $q$, and it is not specified for other values of $q$.

## Sources

- Pasquale Petrullo and Domenico Senato, *Generalized Eulerian Polynomials with a Nonnegative Gamma Vector*, Journal of Integer Sequences 27 (2024), Article 24.1.5, Equation (2).
