# Two cells of one donor have covariance the donor variance

Cells are indexed by pairs $i = (d, c)$ of a donor $d \in \delta$ and a cell slot $c \in \kappa$.
Let $\mu$ be a measure on $\Omega$ and let the cell values $Y_i : \Omega \to \mathbb{R}$ form a
[random-intercept model](is-random-intercept.md) under $\mu$ with donor variance $\sigma_b^2$ and
residual variance $\sigma_e^2$. Variances and covariances are taken with respect to $\mu$,
$\mathrm{Cov}(X, X') = \int (X - \int X\, d\mu)(X' - \int X'\, d\mu)\, d\mu$ and
$\mathrm{Var}\, X = \mathrm{Cov}(X, X)$, the usual ones when $\mu$ is a probability measure. Then
two distinct cells $(d, c)$ and $(d, c')$, $c \ne c'$, of the same donor have covariance

$$\mathrm{Cov}\bigl(Y_{(d, c)}, Y_{(d, c')}\bigr) = \sigma_b^2.$$
