# Survival of the EpiSLFV epidemic at large reproduction number

**Setting.** The $(\gamma,\nu)$-EpiSLFV process on $\mathbb R^d$ with recovery rate $\gamma$ and event measure $\nu(dr,du)=\delta_{\mathcal R}(dr)\,\mu(du)$: every infection event has the same radius $\mathcal R>0$ and its impact $u\in(0,1]$ is drawn from a finite measure $\mu$. Its reproduction number is $\mathrm R_0=\gamma^{-1}V_{\mathcal R}\int_0^1u\,\mu(du)$, where $V_{\mathcal R}$ is the volume of a ball of radius $\mathcal R$.

**Theorem.** There is a constant $\mathrm R_0^{\max}(d)\ge 1$ depending only on the dimension such that for all $\gamma,\mathcal R>0$, every finite $\mu$ and every endemic initial condition (healthy density bounded away from $1$ almost everywhere), if

$$\mathrm R_0(\gamma,\delta_{\mathcal R}\mu)>\mathrm R_0^{\max}(d),$$

then the EpiSLFV process does not go extinct: the expected infected mass on compact sets of positive volume does not tend to $0$.

**Dual statement.** Under the same condition the ancestral process of infected lineages started from one lineage at the origin survives forever with positive probability.

**Extinction does not depend on the initial condition.** For an endemic initial condition, $\lim_t\mathbb E\langle\mathbf 1_A,1-\omega_{M_t}\rangle=\mathrm{Vol}(A)\lim_t\mathbf P(N_t>0)$, where $N_t$ is the number of lineages of the ancestral process started from one lineage. Hence extinction from any endemic start is equivalent to extinction of the dual.

## Depends on

- [EpiSLFV process and its reproduction number](epislfv-process-and-its-reproduction-number.md)

## Expansion

By duality the expected healthy density at a point equals $\mathbb E[\prod_{j\le N_t}\omega_{M^0}(\xi_j)]$ over the positions $\xi_j$ of the ancestral lineages; with an endemic start each factor is at most $1-\varepsilon$, so the expected infected density is bounded below by a multiple of $\mathbf P(N_t>0)$ once the number of surviving lineages is shown to grow without bound on survival. The dual is not exactly a branching process, because the branching rate of a lineage depends on nearby lineages (competition), so survival is proved for $\mathrm R_0$ above a dimension-dependent constant rather than above $1$. The time and space scaling invariances of the process show that only $\mathrm R_0$, not $\gamma$ or $\mathcal R$ separately, enters the threshold.

## Sources

- A. Louvet, B. Wiederhold, "A new stochastic SIS-type modelling framework for analysing epidemic dynamics in continuous space", *Stochastic Processes and their Applications* 195 (2026), 104896, Theorem 2.16, Proposition 2.9, Corollary 3.15, Proposition 2.18, <https://doi.org/10.1016/j.spa.2026.104896> (preprint arXiv:2502.02106).
