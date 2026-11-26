# Wolbachia infection-frequency threshold

Let $x(t)$ and $y(t)$ be the numbers of Wolbachia-infected and uninfected mosquitoes, with perfect maternal transmission, complete cytoplasmic incompatibility and equal sex ratio. With birth rates $b_I, b_U$, density-independent death rates $\delta_I, \delta_U$ and a common density-dependent death rate $d$, the model is (Eq. 1)

$$\frac{dx}{dt} = (b_I - \delta_I)\, x - d\, x (x + y), \qquad \frac{dy}{dt} = b_U\, \frac{y}{x + y}\, y - \delta_U\, y - d\, y (x + y),$$

where $y / (x + y)$ is the probability that an uninfected female mates with an uninfected male. Assume $b_I > d + \delta_I$, $b_U > d + \delta_U$ (Eq. 2) and the strict fitness cost $b_U \ge b_I$, $\delta_I \ge \delta_U$ with $b_U - b_I + \delta_I - \delta_U > 0$ (so $p^* > 0$; in the no-cost equality case $b_U = b_I$ and $\delta_I = \delta_U$, $p^* = 0$, $E_3$ collapses onto $E_1$, $\dot p = b_U p^2(1-p)$, and $p(t) \to 1$ for every $p(0) > 0$), and set $\kappa = (b_I - \delta_I)/d$.

**Equilibria.** Under the strict cost $p^* > 0$, the system has the locally stable equilibria $E_1 = \big(0, (b_U - \delta_U)/d\big)$ (uninfected only) and $E_2 = (\kappa, 0)$ (infected only), and the saddle

$$E_3 = \Big( \frac{\kappa\,(b_U - \delta_U - b_I + \delta_I)}{b_U},\ \frac{\kappa\,(b_I - \delta_I + \delta_U)}{b_U} \Big).$$

**Infection frequency.** The frequency $p = x/(x + y)$ satisfies (Eq. 5)

$$\frac{dp}{dt} = p(1 - p)\big( b_I - \delta_I + \delta_U - b_U (1 - p) \big) = b_U\, p (1 - p) \big(p - p^*\big), \qquad p^* = 1 - \frac{b_I - \delta_I + \delta_U}{b_U}.$$

If $p(0) > p^*$ then $p(t) \uparrow 1$ (Wolbachia fixation), and if $0 < p(0) < p^*$ then $p(t) \downarrow 0$. The line $p = p^*$, i.e.

$$y = \frac{b_I - \delta_I + \delta_U}{b_U - b_I + \delta_I - \delta_U}\, x \qquad \text{(Eq. 6)},$$

is the separatrix between the basins of attraction of $E_1$ (above) and $E_2$ (below).

## Depends on

This node has no prerequisites.

## Proof depends on

Its proof consists of the steps listed under Expansion.

## Expansion

Differentiating $p = x/(x + y)$ gives $p' = (x'y - xy')/(x + y)^2$; the common density-dependent term $d(x + y)$ cancels, leaving the per-capita growth difference $(b_I - \delta_I) - (b_U (1 - p) - \delta_U)$. Because this difference is increasing in $p$, the frequency dynamics is bistable with the unstable interior point $p^*$, the classical invasion threshold of cytoplasmic incompatibility. At an interior equilibrium the $x$-equation forces $x + y = \kappa$ and the frequency equation forces $p = p^*$, which yields $E_3$.

## Sources

- L. Hu, C. Yang, Y. Hui, et al., *Mosquito control based on pesticides and endosymbiotic bacterium Wolbachia*, Bull. Math. Biol. (2021). <https://doi.org/10.1007/s11538-021-00881-9> (PMCID: PMC8043933)
