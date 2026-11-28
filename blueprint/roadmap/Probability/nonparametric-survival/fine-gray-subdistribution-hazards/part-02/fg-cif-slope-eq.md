# Slope factor of the Fine–Gray cumulative incidence curve in terms of the curve

Let $\iota$ be a set of grid indices, $x, b \in \mathbb{R}$ a scalar covariate value and a coefficient, and $\Lambda : \iota \to \mathbb{R}$ baseline cumulative subdistribution hazard values. The [Fine–Gray cumulative incidence curve](fg-cif.md) is $F_j = 1 - \exp(-e^{bx}\Lambda_j)$ and its [slope factor](fg-cif-slope.md) is $s_j = \exp(-e^{bx}\Lambda_j)\, e^{bx}$, for $j \in \iota$.

For every $x$, $b$, $\Lambda$ and every $j \in \iota$,

$$
s_j = (1 - F_j)\, e^{bx}.
$$
