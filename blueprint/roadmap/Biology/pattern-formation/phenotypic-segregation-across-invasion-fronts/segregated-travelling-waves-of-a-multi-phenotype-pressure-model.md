# Segregated travelling waves of a multi-phenotype pressure model

**Model.** Cells of phenotypes $i = 1, \dots, I$ have volume fractions $n_i(t,x)$ on $x \in \mathbb R$ and contribute with weights $\omega_i > 0$ to the pressure $p = \sum_i \omega_i n_i$. They move down the pressure gradient with mobilities $\mu_i > 0$ and divide or die at rates regulated by pressure:

$$\partial_t n_i - \mu_i\,\partial_x\big(n_i\,\partial_x p\big) = \alpha_i\,G(p)\,n_i,$$

where $G(0) < \infty$, $G(\bar p) = 0$ at the homeostatic pressure $\bar p > 0$, and $G' < 0$ (assumption 6). Only phenotype $1$ proliferates on the relevant time scale, $\alpha_1 > 0$ and $\alpha_i = 0$ for $i \ge 2$ (assumption 7), and mobility increases with the index, $0 < \mu_1 < \mu_2 < \cdots < \mu_I$ (assumption 13): a proliferation–migration trade-off. This system is the formal continuum limit of an on-lattice branching biased random walk in which a cell moves to a neighbouring site with probability proportional to the positive part of the pressure difference, scaled by a phenotype-dependent sensitivity $\gamma_i$, under the scaling $\gamma_i\Delta x^2/(2\tau\bar p) \to \mu_i$.

**Theorem.** Under assumptions (6), (7) and (13), for any masses $M_2, \dots, M_I > 0$ there exist interface positions $0 = z_1 < z_2 < \cdots < z_I$ and a speed $c > 0$ such that the travelling-wave system for $n_i(z)$, $z = x - ct$, has a solution with
- $n_i > 0$ on $(z_{i-1}, z_i)$ and $n_i = 0$ outside it ($z_0 = -\infty$), each $n_i$ continuous and decreasing there, $\int_{z_{i-1}}^{z_i} n_i = M_i$ for $i \ge 2$, and $p(-\infty) = \bar p$;
- pressure $p$ positive, continuous and decreasing on $(-\infty, z_I)$, with

$$p(0) = \Big(2c\sum_{j=2}^{I}\frac{\omega_j M_j}{\mu_j}\Big)^{1/2},$$

and with kinks at the interfaces given by the matching conditions

$$-\mu_{i+1}\,p'(z_i^+) = -\mu_i\,p'(z_i^-) = c, \qquad i = 1, \dots, I-1.$$

So phenotype $1$ fills the rear of the wave and phenotypes of increasing mobility occupy successive bands toward the invading edge.

## Expansion

On the support of each phenotype only one species is present, so $p = \omega_i n_i$ there and the travelling-wave equation becomes a scalar equation for $p$: in the rear, $-c p' - \mu_1(p p')' = \alpha_1 G(p)\,p$, a porous-medium-type equation with a pressure-limited source whose solution decreases from $\bar p$; in the non-proliferating bands, mass conservation integrates to $-c\,n_i = \mu_i n_i p'$, i.e. $p' = -c/\mu_i$, so the pressure is linear with slope $-c/\mu_i$ and steeper for less mobile phenotypes. Continuity of the pressure and of the flux at each interface gives the kink conditions; on band $j$ the mass is $M_j = \mu_j(p(z_{j-1})^2 - p(z_j)^2)/(2c\,\omega_j)$, and summing with $p(z_I) = 0$ gives the value of $p(0)$; imposing the masses $M_i$ fixes the interface positions; a shooting argument in $c$ matches the rear solution to the front, as in the single-phenotype case. Segregation requires the ordering of mobilities: a more mobile phenotype behind a less mobile one would overtake it. Numerical simulations of the individual-based model agree closely with the travelling-wave profiles.

## Sources

- J. A. Carrillo, T. Lorenzi, F. R. Macfarlane, "Spatial segregation across travelling fronts in individual-based and continuum models for the growth of heterogeneous cell populations", Bulletin of Mathematical Biology 87 (2025) 77, Eqs. (6)–(9), (13)–(20), Remark 2 and Theorem 1 (eight-step proof), <https://doi.org/10.1007/s11538-025-01452-y>, PMCID PMC12089248.
