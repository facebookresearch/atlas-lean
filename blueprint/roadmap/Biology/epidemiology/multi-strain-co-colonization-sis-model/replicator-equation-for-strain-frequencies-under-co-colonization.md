# Replicator equation for strain frequencies under co-colonization

In the [N-strain co-colonization SIS model](n-strain-sis-model-with-co-colonization.md) with $R_0 > 1$, write the co-colonization factors as small perturbations of a common value,

$$K_{ij} = k + \varepsilon\,\alpha_{ij}, \qquad 0 < \varepsilon \ll 1,$$

with $A = (\alpha_{ij})$. On the slow time scale $\tau = \varepsilon t$, the strain frequencies $z = (z_1, \dots, z_N)$ in the simplex $\{z \in [0,1]^N : \sum_i z_i = 1\}$ obey

$$\frac{dz_i}{d\tau} = \Theta\, z_i\Bigl(\sum_{j=1}^N \bigl[\mu(\alpha_{ji} - \alpha_{ij}) + \alpha_{ji}\bigr] z_j - z^\top A z\Bigr), \qquad \Theta = \frac{\beta T^* I^* D^*}{2(T^*)^2 - I^* D^*}, \quad \mu = \frac{I^*}{D^*} = \frac{1}{k(R_0 - 1)}. \tag{10}$$

With $M = \mu(A^\top - A) + A^\top$, and since $z^\top (A^\top - A) z = 0$, this is the replicator equation with payoff matrix $M$:

$$\frac{dz_i}{d\tau} = \Theta\, z_i\bigl((Mz)_i - z^\top M z\bigr). \tag{11}$$

By Tikhonov-type quasi-stationarity, solutions of the full epidemiological system track the slow–fast reduction as $\varepsilon \to 0$. Competition among strains is thus decided by asymmetries in the co-colonization interactions, weighted by the mean-field quantities $R_0$ and $k$ through $\mu$, while $\Theta$ only sets the speed.

## Depends on

- [N-strain SIS model with co-colonization](n-strain-sis-model-with-co-colonization.md)
- [Solution of the replicator equation](../../population-dynamics/replicator-dynamics/is-solution.md)

## Expansion

Equation (11) follows from (10) because $(Mz)_i = \sum_j [\mu(\alpha_{ji} - \alpha_{ij}) + \alpha_{ji}] z_j$ and $z^\top M z = \mu\, z^\top(A^\top - A) z + z^\top A^\top z = z^\top A z$, the antisymmetric part contributing nothing. The slow equation itself comes from expanding the $(I_i, J_i)$ system to first order in $\varepsilon$ around the neutral manifold $H_i = 0$ and projecting onto the conserved coordinates $z_i$.

## Sources

- S. Madec and E. Gjini, *Predicting N-strain coexistence from co-colonization interactions: epidemiology meets ecology and the replicator equation*, Bull. Math. Biol. (2020), <https://doi.org/10.1007/s11538-020-00816-w>, PMCID PMC7595998 (Section 3.1, equations (10) and (11); Table 1).
