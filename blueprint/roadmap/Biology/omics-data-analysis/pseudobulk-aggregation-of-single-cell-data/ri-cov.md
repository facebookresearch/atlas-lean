# Random-intercept covariance kernel

Cells are indexed by pairs $i = (d, c)$ of a donor $d \in \delta$ and a cell slot $c \in \kappa$.
For real $\sigma_b^2$ and $\sigma_e^2$, the random-intercept covariance of the cells $i = (d, c)$
and $j = (d', c')$ is

$$k(i, j) = \sigma_b^2\, [d = d'] + \sigma_e^2\, [i = j],$$

where $[P]$ is $1$ if $P$ holds and $0$ otherwise: $\sigma_b^2 + \sigma_e^2$ for $i = j$,
$\sigma_b^2$ for two distinct cells of one donor and $0$ for cells of different donors. It is
defined for all real $\sigma_b^2$ and $\sigma_e^2$; the
[random-intercept model](is-random-intercept.md) has both nonnegative.
