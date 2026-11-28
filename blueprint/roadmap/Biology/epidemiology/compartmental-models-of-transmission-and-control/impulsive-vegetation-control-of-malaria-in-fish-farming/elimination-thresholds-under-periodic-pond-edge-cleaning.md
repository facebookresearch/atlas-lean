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

**Mosquito threshold.** Replace $V$ by $V_{\mathrm{per}}$, write $\tilde K_p(t)=K_p(V_{\mathrm{per}}(t))$, $\tilde K_w(t)=K_w(V_{\mathrm{per}}(t))$ and $M=M_S+M_I$, so that $(L_p,L_w,M)$ solves the $\tau$-periodic system $\dot L_p=\alpha\frac{\tilde K_p}{\tilde K_w+\tilde K_p}M(1-L_p/\tilde K_p)-(\nu+\mu_L+\mu_p(1-V_{\mathrm{per}}))L_p$, $\dot L_w=\alpha\frac{\tilde K_w}{\tilde K_w+\tilde K_p}M(1-L_w/\tilde K_w)-(\nu+\mu_L)L_w$, $\dot M=\nu(L_p+L_w)-\mu_MM$, on the set $K_X$ where $L_p\le\tilde K_p$, $L_w\le\tilde K_w$ and $M\le\frac{\nu}{\mu_M}\big(\max_{[0,\tau)}\tilde K_p+\max_{[0,\tau)}\tilde K_w\big)$. Let $\mathcal N=\dfrac{\alpha\nu}{\mu_M(\nu+\mu_L)}$ (the basic offspring number) and $\mathcal N_p(t)=\dfrac{\nu\alpha}{\mu_M(\nu+\mu_L+\mu_p(1-V_{\mathrm{per}}(t)))}$, and $\theta=\dfrac{\tilde K_w(\tau^-)+\tilde K_p(\tau^-)}{\tilde K_w(0)+\tilde K_p(0)}$.

1. If $\displaystyle \mathcal N\max_{t\in[0,\tau)}\frac{\tilde K_w}{\tilde K_w+\tilde K_p}+\mathcal N_p(\tau^-)\max_{t\in[0,\tau)}\frac{\tilde K_p}{\tilde K_w+\tilde K_p}\le1$, every trajectory starting in $K_X$ tends to $0$ (mosquito extinction).
2. If $\displaystyle \frac{\min_{[0,\tau)}\tilde K_w/(\tilde K_w+\tilde K_p)}{\mathcal N^{-1}+\theta}+\frac{\min_{[0,\tau)}\tilde K_p/(\tilde K_w+\tilde K_p)}{\mathcal N_p(0)^{-1}+\theta}>1$, every solution starting in $K_X\setminus\{0\}$ is bounded above and below by asymptotically periodic solutions.

The source observes positive periodic mosquito behaviour numerically but does not prove that a periodic mosquito solution exists.

**Disease threshold.** Assume that the mosquito system has a strictly positive $\tau$-periodic solution $M_{\mathrm{per}}$ (this is an assumption, not a consequence of item 2), and let the infected components follow $\dot M_I=\beta_{hv}I(M_{\mathrm{per}}-M_I)-\mu_MM_I$, $\dot I=\beta_{vh}(1-I)M_I-\kappa I$ on $K_Y=\{0\le M_I\le M_{\mathrm{per}}(t),\ 0\le I\le1\}$. Then

$$\max_{t\in[0,\tau)}\sqrt{\frac{\beta_{vh}\beta_{hv}M_{\mathrm{per}}(t)}{\kappa\,\mu_M}}\le1\ \Longrightarrow\ (M_I,I)\to0,\qquad \min_{t\in[0,\tau)}\sqrt{\frac{\beta_{vh}\beta_{hv}M_{\mathrm{per}}(t)}{\kappa\,\mu_M}}>1\ \Longrightarrow$$

a strictly positive periodic solution attracting all initial conditions in $K_Y\setminus\{0\}$.

## Expansion

Between cleanings the larva–mosquito subsystem and the infection subsystem $(M_I,I)$ are cooperative with concave nonlinearities, so a threshold theorem for periodic cooperative concave systems applies: the trivial solution is globally attracting if the linearization at $0$ has nonpositive growth over a period, and a unique positive periodic orbit is globally attracting otherwise. Bounding the periodic linearization by its constant extremes over a period gives the max/min conditions; the square-root quantity is the vector–host reproduction number $\sqrt{(\beta_{hv}M/\mu_M)(\beta_{vh}/\kappa)}$ evaluated along $M_{\mathrm{per}}$. More frequent cleaning (smaller $\tau$) keeps $V_{\mathrm{per}}$ low, which raises pond larval mortality and lowers $M_{\mathrm{per}}$.

## Sources

- Felipe J. P. Antunes, M. Soledad Aronna, Cláudia T. Codeço, "Modeling and control of malaria dynamics in fish farming regions", arXiv:2010.14366 (2020), Section 2 (model) and Section 3 (Proposition 3.1 on periodic vegetation, Theorem 3.2 on the mosquito population, Remark 3.3, and Theorem 3.4 on the limit behaviour of the disease), <https://doi.org/10.48550/arXiv.2010.14366>.
