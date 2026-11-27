# Evolutionarily stable fraction of migrants under a migrant Allee effect

**Model.** Eggs $x_1$, migrant adults $x_M$ and resident (non-migrant) adults $x_N$ evolve by the stage-structured map

$$x_1(t+1) = f_M(z_M)x_M + f_N(z_N)x_N, \qquad x_M(t+1) = \phi s_M x_1, \qquad x_N(t+1) = (1 - \phi)s_N x_1,$$

where a fraction $\phi \in [0, 1]$ of surviving eggs become migrants, $s_M, s_N$ are survival probabilities, and competition is felt through $z_M = x_M + p x_N$ and $z_N = x_N + q x_M$ with $0 < p, q < 1$. Migrant fecundity $f_M$ is unimodal (an Allee effect: increasing at low density, maximal at $C_0$, with $s_M f_M(C_0) > 1$), and resident fecundity $f_N$ is decreasing with $s_N f_N(0) > 1$. Let $\tilde x_N$ solve $s_N f_N(z) = 1$ (resident carrying capacity) and $\hat x_M$ be the stable positive solution of $s_M f_M(z) = 1$ (migrant carrying capacity). The strategy evolves by the Lande-type equation $\phi(t+1) = \phi(t) + \frac{\sigma^2}{2R_0}\,\partial_v R_0(x(t), v)|_{v = \phi(t)}$, with $R_0$ the inherent net reproductive number.

**Theorem.** Under the standing hypotheses on $f_M, f_N$:
1. *(Ecological dynamics.)* With $\phi_1 = \dfrac{1 - s_N f_N(0)}{s_M f_M(0) - s_N f_N(0)}$, the extinction state is unstable for $\phi \in [0, \phi_1)$ and locally stable for $\phi \in (\phi_1, 1]$; a strong migrant Allee effect thus creates bistability when migration is common.
2. *(ESS.)* If $\sigma^2 > 0$, $q\hat x_M < \tilde x_N$ and $p\tilde x_N < \hat x_M$, the eco-evolutionary system has an equilibrium $(x^*(\phi^*), \phi^*)$ with

$$\phi^* = \frac{\rho}{\rho + s_M/s_N}, \qquad \rho = \frac{\hat x_M - p\tilde x_N}{\tilde x_N - q\hat x_M},$$

where $x^*(\phi^*)$ is the unique stable positive fixed point of the ecological map at $\phi = \phi^*$. For small $\sigma^2 > 0$ it is locally asymptotically stable, so $\phi^*$ is the unique evolutionarily stable strategy, and it is also the unique ideal free distribution of the population between the two morphs.

## Expansion

At an evolutionary equilibrium the per-capita fitness of migrants and residents must be equal, $s_M f_M(z_M) = s_N f_N(z_N) = 1$, which pins $z_M = \hat x_M$ and $z_N = \tilde x_N$. Solving the linear competition relations for the adult densities gives $x_M/x_N = \rho$, and since $x_M/x_N = \phi s_M/((1 - \phi)s_N)$ this yields the formula for $\phi^*$; the two carrying-capacity inequalities make both densities positive. Partial migration, the coexistence of both morphs, is therefore stable despite the Allee effect, provided migrants start above the Allee threshold.

## Sources

- Yogesh Trivedi, Ram Singh and Anushaya Mohapatra, "The evolutionary stability of partial migration with Allee effects", Journal of Difference Equations and Applications 30 (2024), 1172–1193, <https://doi.org/10.1080/10236198.2024.2339334>; numbering as in arXiv:2203.00321: Theorems 2.10, 3.1, 3.3 and 4.2.
