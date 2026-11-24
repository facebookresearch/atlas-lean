# Truncated first Rogers–Ramanujan identity

Work in the ring $\mathbb{Q}[[X]]$ of formal power series and write $(X; X)_m = \prod_{i=1}^{m} (1 - X^i)$, so $(X; X)_0 = 1$; each $(X; X)_m$ has constant term $1$ and is invertible. For a natural number $r$ let $\varepsilon_0 = 1$ and, for $r \ge 1$,

$$\varepsilon_r = (-1)^r \bigl(X^{5\binom{r}{2} + 2r} + X^{5\binom{r}{2} + 3r}\bigr) = (-1)^r \bigl(X^{r(5r-1)/2} + X^{r(5r+1)/2}\bigr).$$

Then for every natural number $n$, $X^{n+1}$ divides

$$(X; X)_n \sum_{j=0}^{n} \frac{X^{j^2}}{(X; X)_j} - \sum_{r=0}^{n} \varepsilon_r,$$

that is, the two power series agree in every coefficient of degree at most $n$.
