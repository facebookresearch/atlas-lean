# Minimal cost of eradication in the kernel SIS model

**Setting.** Use the infinite-dimensional SIS model, the vaccination strategies $\eta\in\Delta$ (fraction left unvaccinated), the effective reproduction number $R_e$, the endemic prevalence $I$ and the uniform cost $C(\eta)=1-\int_\Omega\eta\,d\mu$ from [Pareto frontier of vaccination cost against reproduction number or endemic prevalence](pareto-frontier-of-vaccination-cost-against-reproduction-number-or-endemic-prevalence.md). Let $\mathfrak{g}$ be the maximal endemic equilibrium without vaccination and $C^\star_L(\ell)=\min\{C(\eta):L(\eta)\le\ell\}$.

**Theorem.** Assume $R_0>1$.

1. A strategy $\eta$ is Pareto optimal for $(R_e,C)$ with $R_e(\eta)=1$ if and only if it is Pareto optimal for $(I,C)$ with $I(\eta)=0$. Hence eradication strategies do not depend on the loss, and

$$C^\star_{R_e}(1)=C^\star_I(0).$$

2. The uniform strategy $\eta\equiv1/R_0$ and the endemic-profile strategy $\eta=1-\mathfrak{g}$ are both critical ($R_e=1$), so the minimal fraction of the population that must be vaccinated to eradicate the infection satisfies

$$C^\star_I(0)\le\min\Big(1-\frac{1}{R_0},\ \int_\Omega\mathfrak{g}\,d\mu\Big)=\min\Big(1-\frac{1}{R_0},\ I(1)\Big).$$

## Expansion

Part 1 follows from $I(\eta)=0\iff R_e(\eta)\le1$: any strategy with zero prevalence has $R_e\le1$, and continuity plus monotonicity of $R_e$ under the uniform cost forces a cost-minimal one to sit exactly at $R_e=1$. For part 2, homogeneity of the spectral radius gives $R_e(1/R_0)=R_0/R_0=1$ at cost $1-1/R_0$, while vaccinating each feature class in proportion to its endemic prevalence is critical by the maximal-equilibrium characterization and costs $\int\mathfrak{g}\,d\mu$, the endemic prevalence without vaccination. Neither bound dominates in general; examples such as a multipartite graphon kernel show that optimal strategies can vaccinate far less than either.

## Depends on

- [Pareto frontier of vaccination cost against reproduction number or endemic prevalence](pareto-frontier-of-vaccination-cost-against-reproduction-number-or-endemic-prevalence.md)

## Sources

- Jean-François Delmas, Dylan Dronnier, Pierre-André Zitt, "Targeted Vaccination Strategies for an Infinite-dimensional SIS Model", arXiv:2103.10330 (2021): Section 1.4 (main results: the remark that eradication strategies do not depend on the loss, the remark on the minimal cost of eradication, the critical-allocation theorem for the maximal equilibrium) and Section 2 (proposition on the maximal equilibrium). <https://doi.org/10.48550/arXiv.2103.10330>
