# Derivative of the Fine–Gray cumulative incidence map along a coefficient perturbation

Let $\iota$ be a set of grid indices, $x, b \in \mathbb{R}$ a scalar covariate value and a coefficient, and $\Lambda : \iota \to \mathbb{R}$ baseline cumulative subdistribution hazard values. The [Fine–Gray cumulative incidence curve](fg-cif.md) is $F_j = 1 - \exp(-e^{bx}\Lambda_j)$ and its [slope factor](fg-cif-slope.md) is $s_j = \exp(-e^{bx}\Lambda_j)\, e^{bx}$, for $j \in \iota$. The [derivative of the cumulative incidence map](fg-cif-deriv.md) at $(b, \Lambda)$ is the continuous linear map $D$ from $\mathbb{R} \times \mathbb{R}^{\iota}$ to $\mathbb{R}^{\iota}$ (product topology) given by $D(h, H)_j = s_j\,(x \Lambda_j h + H_j)$.

For every $x$, $b$, $\Lambda$ and every $t \in \mathbb{R}$, the derivative applied to the pure coefficient perturbation $(t, 0)$ is

$$
D(t, 0) = \bigl( s_j\, x \Lambda_j\, t \bigr)_{j \in \iota}.
$$
