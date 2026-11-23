# With nonzero donor variance cells of one donor are dependent

Cells are indexed by pairs $i = (d, c)$ of a donor $d \in \delta$ and a cell slot $c \in \kappa$.
Let $\mu$ be a measure on $\Omega$ and let the cell values $Y_i : \Omega \to \mathbb{R}$ form a
[random-intercept model](is-random-intercept.md) under $\mu$ with donor variance $\sigma_b^2$ and
residual variance $\sigma_e^2$, with $\sigma_b^2 \ne 0$. Then two distinct cells $(d, c)$ and
$(d, c')$, $c \ne c'$, of the same donor are not independent under $\mu$: independence would make
their [covariance](covariance-same-donor.md) $\sigma_b^2$ vanish. Cells of one donor are therefore
not independent replicates.
