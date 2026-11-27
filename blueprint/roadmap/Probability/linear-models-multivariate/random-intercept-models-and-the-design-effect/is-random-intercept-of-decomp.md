# A donor effect plus residual decomposition is a random-intercept model

Cells are indexed by pairs $i = (d, c)$ of a donor $d \in \delta$ and a cell slot $c \in \kappa$.
Let $\mu$ be a probability measure on $\Omega$, let $\sigma_b^2 \ge 0$, $\sigma_e^2 \ge 0$ and $a$
be real, and let the donor effects $b_d$ and the residuals $e_i$ be square-integrable real random
variables with $\mathrm{Cov}(b_d, b_{d'}) = \sigma_b^2 [d = d']$,
$\mathrm{Cov}(e_i, e_j) = \sigma_e^2 [i = j]$ and $\mathrm{Cov}(b_d, e_j) = 0$ for all donors and
cells. Then $Y_{(d, c)} = a + b_d + e_{(d, c)}$ is a
[random-intercept model](is-random-intercept.md) with donor variance $\sigma_b^2$ and residual
variance $\sigma_e^2$.
