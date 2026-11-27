# Optimal minimal-release strategy for the sterile insect technique

**Model.** Reducing a stage-structured mosquito model (eggs, males, fertilized females, sterile males) by fast egg and male dynamics gives, for fertilized females $F$ and released sterile males $M_s$ under the release rate $u(t) \ge 0$,

$$\frac{dF}{dt} = f(F, M_s), \qquad \frac{dM_s}{dt} = u - \delta_s M_s,$$

$$f(F,M_s) = \frac{\nu(1-\nu)\beta_E^2\nu_E^2F^2}{\big(\frac{\beta_E F}{K} + \nu_E + \delta_E\big)\big((1-\nu)\nu_E\beta_E F + \delta_M\gamma_s M_s\big(\frac{\beta_E F}{K} + \nu_E + \delta_E\big)\big)} - \delta_F F,$$

with oviposition rate $\beta_E$, hatching rate $\nu_E$, female proportion $\nu$, egg carrying capacity $K$, death rates $\delta_E, \delta_M, \delta_F, \delta_s$, and mating competitiveness $\gamma_s$ of sterile males. Assume

$$\delta_s > \delta_M, \qquad \mathcal R_0 = \frac{\nu\beta_E\nu_E}{\delta_F(\nu_E + \delta_E)} > 1,$$

and start at the wild persistence equilibrium $F(0) = \bar F$, $M_s(0) = 0$. A constant release above

$$U^* = \mathcal R_0\,\frac{K(1-\nu)\nu_E\delta_s}{4\gamma_s\delta_M}\Big(1 - \frac1{\mathcal R_0}\Big)^2$$

drives $F \to 0$. For $T > 0$, $\bar U > U^*$ and a target $\varepsilon \in (0, \bar F)$, minimize the total number of released mosquitoes $J(u) = \int_0^T u(t)\,dt$ over controls $0 \le u \le \bar U$ with $F(T) \le \varepsilon$.

**Theorem.** Assume in addition $2\delta_s > \delta_F$. There is a minimal horizon $\bar T > 0$ such that for every $T \ge \bar T$ the problem has a solution $u^*$, with optimal value at most $\bar U\,\bar T$, non-increasing in $T$ and in $\bar U$. For $T > \bar T$ and $\bar U$ large enough there are $0 \le t_0 \le t_1 \le T$ with

1. $u^* \equiv 0$ or $u^* \equiv \bar U$ on $(0, t_0)$;
2. $u^* \in (0, \bar U)$ on $(t_0, t_1)$, a singular arc given in feedback form by

$$u^* = \Big(\frac{\partial^2 f}{\partial M_s^2}\Big)^{-1}\Big(\frac{\partial f}{\partial M_s}\frac{\partial f}{\partial F} + \delta_s M_s\frac{\partial^2 f}{\partial M_s^2} - f\,\frac{\partial^2 f}{\partial M_s\,\partial F}\Big)\Big|_{(F(t), M_s(t))};$$

3. $u^* \equiv 0$ on $(t_1, T)$.

Moreover there is $T^*(\bar U) > \bar T$ such that for $T > T^*$ the optimizer is unique, $0 < t_0 < t_1 < T$, $u^* = 0$ on $(0, t_0)$, and the optimal cost no longer depends on $T$. Along the optimal trajectory $F$ decreases on $(0,T)$, reaches exactly $F(T) = \varepsilon$ with $F'(T) = 0$, and increases again once releases stop.

So the cheapest strategy is not maximal release: after an idle phase, releases follow a smooth singular feedback law and stop before the horizon, letting the remaining sterile males finish the job.

## Expansion

Existence follows from weak-star compactness of the admissible controls and convexity of the dynamics in $u$. Pontryagin's maximum principle with the switching function $\phi = p_{M_s}$ (adjoint of $M_s$) gives bang–bang or singular arcs. Differentiating $\phi \equiv 0$ twice along a singular arc and using $\partial^2 f/\partial M_s^2 > 0$ (the reproduction term is convex in $M_s$) yields the feedback formula. The condition $2\delta_s > \delta_F$ is used to show that the auxiliary function governing the switches can only have local minima, which rules out more than one singular arc and gives the three-phase structure. Comparison arguments show the terminal constraint is active and $F$ is monotone, and for long horizons the idle initial phase absorbs the extra time, which makes the cost constant in $T$. The full four-compartment system has the same qualitative structure.

## Sources

- Luís Almeida, Michel Duprez, Yannick Privat, Nicolas Vauchelet, "Optimal control strategies for the sterile mosquitoes technique", arXiv (2020). Section 2 (System $\mathcal S_1$, hypothesis $\mathcal H$, $U^*$), Propositions 2.1 and 2.3, Section 3 (problem $\mathcal P^{(\mathcal S_1)}_{T,\bar U,\varepsilon}$), Theorems 3.2, 3.3 and 5.1. <https://doi.org/10.48550/arXiv.2011.04449>. Published version: Journal of Differential Equations 311 (2022), 229–266, <https://doi.org/10.1016/j.jde.2021.12.002>; locators above refer to the arXiv version.
