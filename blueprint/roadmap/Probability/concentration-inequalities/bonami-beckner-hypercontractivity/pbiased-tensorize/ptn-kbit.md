# One-coordinate $p$-biased noise kernel

For real $p, \rho$ and bits $x, y \in \{0, 1\}$,

$$k_{p,\rho}(x, y) = \rho\, \mathbf{1}_{\{x = y\}} + (1 - \rho)\, w_p(y), \qquad w_p(1) = p,\ w_p(0) = 1 - p:$$

for $\rho, p \in [0, 1]$ the transition probability of keeping the bit with probability $\rho$ and
otherwise resampling it from the Bernoulli($p$) law.
