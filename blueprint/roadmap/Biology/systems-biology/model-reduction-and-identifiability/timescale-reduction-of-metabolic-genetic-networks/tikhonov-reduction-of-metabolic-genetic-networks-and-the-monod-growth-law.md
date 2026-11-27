# Tikhonov reduction of metabolic–genetic networks and the Monod growth law

**Model.** A metabolic–genetic network has extracellular nutrients $Y$ (concentrations $y$), intracellular metabolites $X$ and macromolecules (enzymes and other gene products) $P$, linked by uptake reactions $V_y$, metabolic reactions $V_x$ and biomass-producing reactions $V_p$ with stoichiometric matrices $S$. Each rate is enzyme amount times a kinetic term, e.g. $V_y = P f_y(y)$. Metabolism is much faster than gene expression; with the timescale ratio $\varepsilon \ll 1$ and long time $T$, the scaled system is

$$y' = -\frac{1}{\varepsilon\vartheta_e}S^y_y\tilde V_y, \qquad \varepsilon X' = S^x_y\tilde V_y + S^x_x\tilde V_x - \alpha\varepsilon S^x_p\tilde V_p, \qquad P' = S^p_p\tilde V_p,$$

with the rates evaluated at intracellular concentrations $X/\tilde\vartheta_c(T,P)$ and $\alpha$ the metabolite cost of biomass. Growth is chosen by dynamic optimization of the enzyme production fluxes (for example time-minimal growth to a target or a discounted biomass integral).

**Theorem (quasi-steady-state reduction).** Suppose
1. (Condition 1) the quasi-steady-state equation obtained by setting the right-hand side of the $X$ equation to zero at $\varepsilon = 0$ has a locally unique solution $X = q(T, y, P)$ for all admissible $T, y, P$; and
2. (Condition 2) this solution is an exponentially stable equilibrium of the fast (boundary-layer) system, uniformly in $(T, y, P)$;

and the reduced model, obtained by substituting $X = q(T,y,P)$, has a unique solution $(y(T,0), P(T,0))$. Then there is $\varepsilon^* > 0$ such that for every $\varepsilon < \varepsilon^*$ the full model has a unique solution $(y(T,\varepsilon), P(T,\varepsilon))$, and it converges to the reduced solution as $\varepsilon \to 0$. This justifies replacing the metabolite dynamics by the flux-balance constraint $S^x_y V_y + S^x_x V_x = \alpha\varepsilon S^x_p V_p$ inside the dynamic optimization.

**Proposition (Monod law).** In the minimal network $Y \to X$ (rate $V_y = P f_y(y)$) and $\alpha X \to P$ (rate $V_p = P f_p(x)$), if uptake is Michaelis–Menten, $V_y = k_{\mathrm{cat}}Py/(K_m + y)$, then the long-timescale approximation is the Monod growth model

$$\dot Y = -\frac{1}{\varrho}\mu(y)P, \qquad \dot P = \mu(y)P, \qquad \mu(y) = \frac{\mu_{\max}y}{K_y + y},$$

with substrate $Y$, biomass $P$, yield coefficient $\varrho \ge 0$, half-saturation $K_y = K_m$ and $\mu_{\max}$ proportional to $k_{\mathrm{cat}}/\alpha$. The empirical Monod law thus follows from Michaelis–Menten uptake plus timescale separation and growth optimality.

## Proof sketch

The theorem is Tikhonov's singular perturbation theorem applied to the slow variables $(y, P)$ and fast variables $X$: Condition 1 gives the slow manifold and Condition 2 its attractivity, so after an initial layer of duration $O(\varepsilon)$ the trajectory tracks the slow manifold. For the minimal network the quasi-steady state is $V_y = \alpha\varepsilon V_p$, i.e. biomass production is limited by uptake, so $V_p = \frac{1}{\alpha\varepsilon}\frac{k_{\mathrm{cat}}y}{K_m + y}P$, which is proportional to $P$ with a saturating per-biomass rate: exactly $\mu(y)P$. Substrate is consumed at the uptake rate, which is the biomass rate divided by the yield.

## Sources

- Steffen Waldherr, Diego A. Oyarzún and Alexander Bockmayr, "Dynamic optimization of metabolic networks coupled with gene expression", *Journal of Theoretical Biology* 365 (2015), 469–485, <https://doi.org/10.1016/j.jtbi.2014.10.035>. Preprint version: arXiv:1309.4936 (2013), Tikhonov reduction theorem with Conditions 1–2, the minimal metabolic–genetic network and the Monod-model proposition with its proof, <https://doi.org/10.48550/arXiv.1309.4936>.
