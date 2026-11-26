# SARS-CoV-2 within-host model with density-dependent innate killing

**Model.** Susceptible target cells $S$, infected cells $I$, free virus $V$, two precursor compartments $M_1, M_2$ and virus-specific effector cells $E$ evolve by

$$\begin{aligned}
\dot S &= -\beta V S,\\
\dot I &= \beta V S - \delta I^{k} I - m\,\frac{E^{r}}{E^{r} + \phi^{r}}\, I,\\
\dot V &= \pi I - \gamma V,\\
\dot M_1 &= \omega I M_1 - q M_1,\\
\dot M_2 &= q\,(M_1 - M_2),\\
\dot E &= q M_2 - \delta_E E,
\end{aligned}$$

with infection rate $\beta$, per-cell virus production $\pi$, virus clearance $\gamma$, innate killing rate $\delta$ with density exponent $k \ge 0$, maximal adaptive killing $m$ with Hill coefficient $r$ and half-saturation effector level $\phi$, precursor proliferation $\omega$, transition rate $q$ and effector death rate $\delta_E$. Initial conditions are $S_0 = 10^7$ cells/mL, $I_0 = 1$, $V_0 = \pi I_0/\gamma$, $M_1(0) = 1$, $M_2(0) = E(0) = 0$.

**Reduction.** Setting $k = 0$ and $m = 0$ removes density dependence and the adaptive response and gives the target-cell-limited model $\dot S = -\beta VS$, $\dot I = \beta VS - \delta I$, $\dot V = \pi I - \gamma V$, used for influenza.

**Properties.**

1. The nonnegative orthant is invariant and $S$ is nonincreasing.
2. In the reduced model ($k = 0$, $m = 0$) infection grows from a small inoculum iff the within-host basic reproductive number $\beta\pi S_0/(\gamma\delta)$ exceeds $1$. With $k > 0$ the per-cell innate killing rate $\delta I^{k}$ grows with infected-cell density, so killing accelerates as $I$ rises, producing a sharp viral peak followed by rapid decline.
3. The precursor cascade $M_1 \to M_2 \to E$ delays the adaptive response by two stages of mean duration $1/q$ each, after which the saturating term $mE^r/(E^r + \phi^r)$ clears remaining infected cells, ending long low-level shedding plateaus.

## Expansion

Density-dependent clearance $\delta I^{k}I$ makes the effective death rate of infected cells increase with their density, a phenomenological representation of innate responses (e.g. interferon) triggered by infection burden. Combined with variability across individuals in $\beta$, $\delta$, $k$ and $\pi$, the model generates the observed patterns of SARS-CoV-2 shedding: rapid elimination after the peak, a prolonged low plateau, or a prolonged high plateau. These trajectories $V(t)$ are the input to [viral-load-dependent transmission](../../stochastic-network-spatial-and-vector-models/viral-load-dependent-transmission/viral-load-dose-response-model-of-the-individual-reproduction-number.md).

## Sources

- A. Goyal, D. B. Reeves, E. F. Cardozo-Ojeda, J. T. Schiffer, B. T. Mayer, "Viral load and contact heterogeneity predict SARS-CoV-2 transmission and super-spreading events", eLife 10 (2021) e63537, Materials and methods ("SARS-CoV-2 within-host model", "Influenza within-host model"), <https://doi.org/10.7554/eLife.63537> (PMC7929560).
