# Flow-kick bifurcations of a tree–grass model with periodic fire

**Model.** Let $x \ge 0$ be grass and $y \ge 0$ tree biomass, each scaled by its carrying capacity. Between fires they follow the one-sided Lotka–Volterra flow

$$\dot x = x(1 - x - \alpha y), \qquad \dot y = \delta y(1 - y), \qquad \alpha, \delta > 0,$$

whose only stable state for $0 < \alpha < 1$ is the coexistence point $(1-\alpha, 1)$. Every $\tau > 0$ time units a fire applies the kicks

$$x(n\tau^+) = (1-k_1)\,x(n\tau^-), \qquad y(n\tau^+) = \big(1 - k_2\,\omega(k_1 x(n\tau^-))\big)\,y(n\tau^-),$$

with grass kill fraction $k_1 \in [0,1)$, maximal tree kill fraction $k_2 \in [0,1]$ and switching function $\omega(\xi) = \xi^2/(a^2 + \xi^2)$, so tree mortality rises steeply once the burned grass $k_1 x$ exceeds the threshold $a > 0$. Let $\Phi$ be the flow-kick map (flow for time $\tau$, then kick), whose fixed points are the post-fire states of periodic solutions.

**Theorem.**
1. (Grassland) $\Phi$ has a grass-only fixed point $(x_g, 0)$ with

$$x_g = \frac{1 - (1-k_1)e^{\tau}}{1 - e^{\tau}},$$

which lies in the first quadrant exactly when $k_1 \le 1 - e^{-\tau}$; it enters through a transcritical bifurcation with the origin at $k_1 = 1 - e^{-\tau}$.
2. (Grassland–savanna) For $k_1 < 1 - e^{-\tau}$, a necessary condition for a tree–grass coexistence fixed point to cross into the first quadrant through $(x_g, 0)$ is

$$1 - e^{\delta\tau}\big(1 - k_2\,\omega(\xi_g)\big) = 0, \qquad \xi_g = \frac{k_1 x_g}{1 - k_1}.$$

3. (Forest–savanna) $(0,1)$ is a fixed point for all disturbance parameters, and a necessary condition for a coexistence fixed point to cross into the first quadrant through $(0,1)$ is

$$1 - (1-k_1)\,e^{(1-\alpha)\tau} = 0,$$

independent of $k_2$.
4. (Fast-fire limit) With fixed intensities per unit time $r_1 = k_1/\tau$, $r_2 = k_2/\tau$, the flow-kick dynamics converge as $\tau \to 0$ to the flow $\dot x = x(1 - r_1 - x - \alpha y)$, $\dot y = \delta y(1-y)$: frequent mild fires act on grass as extra mortality and, because $\omega(0) = 0$, do not affect trees.

## Expansion

On $y = 0$ the grass follows the logistic flow, so the map is $x \mapsto (1-k_1)xe^{\tau}/(1 + x(e^\tau - 1))$, whose nonzero fixed point is $x_g$. A coexistence branch meets $(x_g,0)$ when the tree-direction multiplier of $\Phi$ there equals 1: a small tree population grows by $e^{\delta\tau}$ during the flow and is multiplied by $1 - k_2\omega(\xi_g)$ at the fire, where $\xi_g$ is the grass burned, i.e. $k_1$ times the pre-fire grass $x_g/(1-k_1)$. At $(0,1)$ a small grass population grows at rate $1 - \alpha$ under full tree cover and loses the fraction $k_1$ at each fire, giving multiplier $(1-k_1)e^{(1-\alpha)\tau}$. Part 4 follows from Taylor-expanding the flow-kick map in $\tau$ and taking the limit of the difference quotient $(\Phi(x,y) - (x,y))/\tau$. Numerical continuation of $\Phi$ further reveals saddle-node curves and four bistable regimes (forest–grassland, forest–savanna, savanna–savanna, grassland–savanna), so the coexistence fixed point need not be unique.

## Sources

- A. Hoyer-Leitzel, S. Iams, "Impulsive fire disturbance in a savanna model: tree–grass coexistence states, multiple stable system states, and resilience", Bulletin of Mathematical Biology (2021), Eqs. (2)–(8), (13) and (17), Table 2, Theorems 1–2 and Lemma 1, <https://doi.org/10.1007/s11538-021-00944-x>, PMCID PMC8484106.
