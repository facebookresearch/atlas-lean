# Crawl-by transients in a pulsed consumer–resource model with group defense

**Model.** Consumers $p_m \ge 0$ and resource $n_m \ge 0$ (nondimensionalized) at reproductive pulse $m$ obey

$$p_{m+1} = \delta_p p_m + \frac{\gamma_p\,p_m n_m}{1 + \sigma n_m^2}, \qquad n_{m+1} = \delta_n n_m \exp\!\Big(-\frac{\gamma_n p_m}{1 + \sigma n_m^2}\Big) + \frac{R\,n_m\,e^{-p_m}}{1 + n_m},$$

with between-pulse survival $\delta_p, \delta_n \in (0,1)$, consumption parameters $\gamma_p, \gamma_n > 0$, group-defense strength $\sigma > 0$ (a Holling type IV response, decreasing for large resource density) and resource recruitment $R > 0$ with Beverton–Holt density dependence. Let $(0, n^*)$ be the resource-only equilibrium and assume $n^* > 1/\sqrt\sigma$ (the density of maximal consumption), so group defense acts below carrying capacity, and $n^* \ne \sqrt{(1-\delta_p)/(\sigma\delta_p)}$ (Appendix A). The equilibria $(0, n^*)$ and a coexistence saddle undergo a transcritical bifurcation at

$$\gamma_p^* = \frac{(1-\delta_p)(1 + \sigma n^{*2})}{n^*};$$

$(0,n^*)$ is stable for $\gamma_p < \gamma_p^*$ and unstable for $\gamma_p > \gamma_p^*$.

**Theorem.**
1. (Global attractor) The system has a compact, connected global attractor in the closed first quadrant.
2. (Crawl-by at resource extinction) Let $\varepsilon \ll 1$. If $p_0$ is of order $\varepsilon^{-1}$ and $n_0$ of order 1, the resource collapses to near zero and recovers only after approximately

$$M = O\!\left(\frac{\log\varepsilon}{\log\delta_p}\right)$$

pulses, the time for consumers to decay by their survival factor $\delta_p$ from order $\varepsilon^{-1}$ to order 1.
3. (Crawl-by at carrying capacity) If $\gamma_p > \gamma_p^*$, set $\lambda_1 = \delta_p + \gamma_p n^*/(1 + \sigma n^{*2}) > 1$. From $(p_0, n_0) = (\varepsilon, n^* - \varepsilon)$, the system stays near $(0, n^*)$ and the resource begins to decline after approximately

$$M = O\!\left(\frac{\log(1/\varepsilon)}{\log\lambda_1}\right)$$

pulses.

For $\gamma_p$ slightly below $\gamma_p^*$, trajectories converge to $(0,n^*)$ only after long pseudo-oscillations (a ghost of the cycle present for $\gamma_p > \gamma_p^*$), whose duration is fitted numerically by a power law $\tau \approx A(\gamma_p^* - \gamma_p)^{-B}$.

## Expansion

The model arises by integrating continuous-time mortality and consumption between pulses and applying a discrete recruitment map at each pulse. Linearizing at $(0, n^*)$, the consumer direction has multiplier $\lambda_1 = \delta_p + \gamma_p n^*/(1+\sigma n^{*2})$, which exceeds 1 exactly when $\gamma_p > \gamma_p^*$; a consumer perturbation of size $\varepsilon$ grows like $\lambda_1^m\varepsilon$ and becomes of order 1 after $\log(1/\varepsilon)/\log\lambda_1$ pulses. At resource extinction the consumer equation reduces to $p_{m+1} \approx \delta_p p_m$, so a consumer density of order $\varepsilon^{-1}$ needs $\log\varepsilon/\log\delta_p$ pulses to fall to order 1 and release the resource. Existence of the global attractor follows from showing the pulse map is point dissipative and compact on the first quadrant (Theorem 2.9 of Magal and Zhao), using that the resource multiplier is below 1 above $n^*$, and connectedness from a result of Gobbino and Sardella.

## Sources

- J. Arroyo-Esquivel, A. Hastings, M. L. Baskett, "Characterizing long transients in consumer-resource systems with group defense and discrete reproductive pulses", Bulletin of Mathematical Biology (2022), Eqs. (4)–(10), Theorems 1–3 and Appendices B–D, <https://doi.org/10.1007/s11538-022-01059-7>, PMCID PMC9376152.
