# Viral-load dose–response model of the individual reproduction number

**Ingredients.** A transmitter has viral load trajectory $V(t)$ (copies/mL), produced by a within-host model. Time is split into steps of length $\Delta t$ (one day).

- **Dose–response.** Given an exposure contact, the viral-load-dependent probability is the Hill function

$$P_t = P[V(t)] = \frac{V(t)^{\alpha}}{\lambda^{\alpha} + V(t)^{\alpha}},$$

with $\lambda > 0$ the viral load giving $50\%$ probability and $\alpha > 0$ the slope. The same form is used for contagiousness (passage of virus to the contact's airway) and for infectiousness (infection given airway exposure); their product is the transmission dose–response curve.
- **Exposure contacts.** The number of exposure contacts in a step, $\eta_{\Delta t}$, is gamma-distributed with mean $\theta\Delta t$, where $\theta$ is the mean daily exposure-contact rate and $\rho$ controls day-to-day dispersion.
- **Transmissions.** The contacts with airway exposure are $\zeta_t = \eta_{\Delta t}P_t$, and the secondary infections in the step are

$$T_{\Delta t} = \mathrm{Ber}(P_t)\, P_t\, \eta_{\Delta t},$$

i.e. with probability $P_t$ the step produces transmissions, and then the number of secondary infections is the infectiousness $P_t$ times the exposure contacts.
- **Individual reproduction number.** Summing over the first 30 days after infection,

$$R_0^{\mathrm{ind}} = \sum_{\Delta t} T_{\Delta t}.$$

**Findings encoded by the model.** Because $P_t$ is a steep sigmoid in $\log V$, transmission concentrates in a short window around peak viral load (for SARS-CoV-2 in the best-fitting regime, infectiousness exceeds the 50% transmission dose for only about 0.5–1.0 day, between days 2 and 6 after infection; transmission is very unlikely below $10^4$–$10^5$ RNA copies), and super-spreader events require a transmitter with high viral load during that window together with a large number of exposure contacts. Heterogeneity in exposure contacts, more than heterogeneity in viral kinetics, reproduces the overdispersed distribution of $R_0^{\mathrm{ind}}$ observed for SARS-CoV-2 but not for influenza.

## Expansion

The model separates two multiplicative sources of variation: viral load enters only through $P_t$, contact behavior only through $\eta_{\Delta t}$. A heavy-tailed $\eta$ multiplies the effect of a high-$P_t$ day, so the distribution of $R_0^{\mathrm{ind}}$ inherits the overdispersion of the contact distribution concentrated on the few days when $V(t)$ exceeds about $\lambda$. Parameters $(\lambda, \alpha, \theta, \rho)$ and the delay $\tau$ from infection to the first infected cell were fitted by grid search to the mean $R_0$, the fraction of transmitters causing most secondary cases, and serial-interval data. Interventions that cut the exposure-contact rate during the high-viral-load window, or that lower peak viral load, shrink the right tail of $R_0^{\mathrm{ind}}$ disproportionately.

## Sources

- A. Goyal, D. B. Reeves, E. F. Cardozo-Ojeda, J. T. Schiffer, B. T. Mayer, "Viral load and contact heterogeneity predict SARS-CoV-2 transmission and super-spreading events", eLife 10 (2021) e63537, Materials and methods ("Dose-response model", "Transmission model and reproduction number") and Results ("Narrow duration of high infectivity", "Requirements for SARS CoV-2 super-spreader events"), <https://doi.org/10.7554/eLife.63537> (PMC7929560).
