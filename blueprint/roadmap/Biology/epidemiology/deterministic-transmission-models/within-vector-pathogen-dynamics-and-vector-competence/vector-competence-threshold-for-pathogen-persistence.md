# Vector-competence threshold for pathogen persistence

**Model.** Let $S_v$ be the susceptible vector population and $P$ the pathogen population, with vector competence $v_c>0$, vector growth rate $\mu_v$, carrying capacity $K$, attack rate $\beta_v$, handling time $E_p$, conversion efficiency $\alpha$ and pathogen inactivation rate $\delta$:

$$\frac{dS_v}{dt}=v_c\mu_vS_v\Big(1-\frac{S_v}{v_cK}\Big)-\frac{\beta_vv_cS_vP}{1+\beta_vv_cE_pS_v},\qquad \frac{dP}{dt}=\frac{\alpha\beta_vv_cS_vP}{1+\beta_vv_cE_pS_v}-\delta P .$$

This is a Rosenzweig–MacArthur predator–prey system with the pathogen as predator.

**Results.** Solutions with $S_v(0),P(0)>0$ stay positive, and there is no vector-free equilibrium with positive pathogen. The disease-free equilibrium $(v_cK,0)$ is globally stable when

$$v_c^2<\frac{\delta}{\beta_vK(\alpha-\delta E_p)}\qquad(\alpha>\delta E_p),$$

so pathogen persistence (endemicity) requires vector competence above $\sqrt{\delta/(\beta_vK(\alpha-\delta E_p))}$.

## Depends on

- [Lotka–Volterra predator–prey model](../../../population-dynamics/lotka-volterra-predator-prey-model/README.md)

## Expansion

At $(v_cK,0)$ the pathogen's per-capita growth rate is $\alpha\beta_vv_c\cdot v_cK/(1+\beta_vv_cE_p\cdot v_cK)-\delta$, which is negative iff $v_c^2\beta_vK(\alpha-\delta E_p)<\delta$; the prey equation is logistic, so the boundary equilibrium is then a stable node. Global stability follows because $S_v\le v_cK$ asymptotically and the pathogen's per-capita rate is increasing in $S_v$, hence eventually negative. Above the threshold a coexistence (endemic) equilibrium appears, whose dependence on $v_c$ and $\delta$ the paper explores numerically.

## Sources

- P. Chathurangika, T. Peiris, L. S. Premadasa, S. S. N. Perera, "Vector Traits Shape Disease Persistence: A Predator Prey Approach to Dengue", *Bulletin of Mathematical Biology* 88(10) (2026), 191, model (2a)–(2b), Theorems 3.1, 3.2 and 3.4, <https://doi.org/10.1007/s11538-026-01764-7> (preprint arXiv:2511.04276).
