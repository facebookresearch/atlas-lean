# Per-cell variance in the random-intercept model

Cells are indexed by pairs $i = (d, c)$ of a donor $d \in \delta$ and a cell slot $c \in \kappa$.
Let $\mu$ be a measure on $\Omega$ and let the cell values $Y_i : \Omega \to \mathbb{R}$ form a
[random-intercept model](is-random-intercept.md) under $\mu$ with donor variance $\sigma_b^2$ and
residual variance $\sigma_e^2$. Variances and covariances are taken with respect to $\mu$,
$\mathrm{Cov}(X, X') = \int (X - \int X\, d\mu)(X' - \int X'\, d\mu)\, d\mu$ and
$\mathrm{Var}\, X = \mathrm{Cov}(X, X)$, the usual ones when $\mu$ is a probability measure. Then
every cell has variance

$$\mathrm{Var}\, Y_i = \sigma_b^2 + \sigma_e^2.$$
