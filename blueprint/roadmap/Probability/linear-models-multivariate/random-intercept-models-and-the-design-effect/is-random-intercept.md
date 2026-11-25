# Random-intercept model of cell values

Cells are indexed by pairs $i = (d, c)$ of a donor $d \in \delta$ and a cell slot $c \in \kappa$.
Let $\mu$ be a measure on a measurable space $\Omega$ and $Y_i : \Omega \to \mathbb{R}$ the cell
values. Variances and covariances are taken with respect to $\mu$,
$\mathrm{Cov}(X, X') = \int (X - \int X\, d\mu)(X' - \int X'\, d\mu)\, d\mu$ and
$\mathrm{Var}\, X = \mathrm{Cov}(X, X)$, the usual ones when $\mu$ is a probability measure. The
family $Y$ is a random-intercept model with donor variance $\sigma_b^2$ and residual variance
$\sigma_e^2$ when $\sigma_b^2 \ge 0$, $\sigma_e^2 \ge 0$, every $Y_i$ is square integrable, and
$\mathrm{Cov}(Y_i, Y_j) = k(i, j)$ for all cells $i, j$, where $k$ is the
[random-intercept kernel](ri-cov.md) $k(i, j) = \sigma_b^2 [d = d'] + \sigma_e^2 [i = j]$. The sign
conditions exclude covariances that no donor random effect produces, such as $Y_{(d, 0)} = Z$ and
$Y_{(d, 1)} = -Z$ for one donor with two cells and $\mathrm{Var}\, Z = 1$, whose kernel would need
$\sigma_b^2 = -1$ and $\sigma_e^2 = 2$.
