# Elimination thresholds for mosquitoes and malaria under periodic pond-edge cleaning

**Model.** In fish-farming regions, artificial ponds become mosquito breeding sites, and vegetation $V\in[0,1]$ on pond edges increases larval carrying capacity. Vegetation regrows and is cut back at cleaning times $n\tau$:

$$\dot V=r(1-V)\ (t\ne n\tau),\qquad V(n\tau^+)=\big(1-\gamma(n\tau)\big)V(n\tau^-),$$

with cleaning intensity $\gamma(t)\to\gamma^*\in[0,1]$. Larvae in ponds ($L_p$) and in other water bodies ($L_w$), susceptible and infected mosquitoes ($M_S,M_I$) and the fractions of susceptible and infected humans ($S,I$, $S+I=1$) satisfy

$$\dot L_p=\alpha\frac{K_p(V)}{K_w(V)+K_p(V)}(M_S+M_I)\Big(1-\frac{L_p}{K_p(V)}\Big)-\big(\nu+\mu_L+\mu_p(1-V)\big)L_p,$$

$$\dot L_w=\alpha\frac{K_w(V)}{K_w(V)+K_p(V)}(M_S+M_I)\Big(1-\frac{L_w}{K_w(V)}\Big)-(\nu+\mu_L)L_w,$$

$$\dot M_S=\nu(L_w+L_p)-\beta_{hv}IM_S-\mu_MM_S,\quad \dot M_I=\beta_{hv}IM_S-\mu_MM_I,\quad \dot I=\beta_{vh}(1-I)M_I-\kappa I,$$

where $\mu_p(1-V)$ is extra larval mortality in cleared ponds (predation by fish).

**Vegetation.** Every trajectory converges to the $\tau$-periodic profile

$$V_{\mathrm{per}}(t)=1-\frac{\gamma^*e^{-r(t-n\tau)}}{1-(1-\gamma^*)e^{-r\tau}},\qquad t\in[n\tau,(n+1)\tau).$$

**Mosquito threshold.** Let $\mathcal N=\dfrac{\alpha\nu}{\mu_M(\nu+\mu_L)}$ (the basic offspring number in non-pond habitats). If the carrying capacities are proportional, $K_p/K_w\equiv\rho$, then

1. $\mathcal N\le1$ implies extinction of the mosquito population for all feasible initial conditions;
2. $\mathcal N>1+\rho$ implies a strictly positive $\tau$-periodic mosquito solution $M_{\mathrm{per}}$ that attracts all nonzero initial conditions.

For general $K_p,K_w$ the same dichotomy holds with conditions mixing $\mathcal N$ and the time-dependent pond offspring number $\mathcal N_p(t)=\dfrac{\nu\alpha}{\mu_M(\nu+\mu_L+\mu_p(1-V_{\mathrm{per}}(t)))}$.

**Disease threshold.** On the periodic mosquito background,

$$\max_{t\in[0,\tau)}\sqrt{\frac{\beta_{vh}\beta_{hv}M_{\mathrm{per}}(t)}{\kappa\,\mu_M}}\le1\ \Longrightarrow\ (M_I,I)\to0,\qquad \min_{t\in[0,\tau)}\sqrt{\frac{\beta_{vh}\beta_{hv}M_{\mathrm{per}}(t)}{\kappa\,\mu_M}}>1\ \Longrightarrow$$

a strictly positive periodic endemic solution attracting all nonzero initial conditions.

## Expansion

Between cleanings the larva–mosquito subsystem and the infection subsystem $(M_I,I)$ are cooperative with concave nonlinearities, so a threshold theorem for periodic cooperative concave systems applies: the trivial solution is globally attracting if the linearization at $0$ has nonpositive growth over a period, and a unique positive periodic orbit is globally attracting otherwise. Bounding the periodic linearization by its constant extremes over a period gives the max/min conditions; the square-root quantity is the vector–host reproduction number $\sqrt{(\beta_{hv}M/\mu_M)(\beta_{vh}/\kappa)}$ evaluated along $M_{\mathrm{per}}$. More frequent cleaning (smaller $\tau$) keeps $V_{\mathrm{per}}$ low, which raises pond larval mortality and lowers $M_{\mathrm{per}}$.

## Sources

- Felipe J. P. Antunes, M. Soledad Aronna, Cláudia T. Codeço, "Modeling and control of malaria dynamics in fish farming regions", arXiv:2010.14366 (2020), Section 2 (model) and Section 3 (Proposition 3.1 on periodic vegetation, Theorem 3.2 and Corollary 3.3 on the mosquito population, and the subsequent theorem on the limit behaviour of the disease), <https://doi.org/10.48550/arXiv.2010.14366>.
