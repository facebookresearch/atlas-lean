# Testing threshold for recurrent epidemics in a polarized, partially vaccinated population

**Model.** A population of $n$ individuals is split into a vaccinated subpopulation (fraction $v$) and a non-vaccinated one. Each individual is susceptible (S), mildly symptomatic infectious (I) or quarantined (Q). Contacts are generated on a continuous-time activity-driven temporal network. Each individual activates at rate $1$ and contacts someone from its own subpopulation with probability $\theta$ (homophily, or polarization) and a uniformly random individual otherwise. Quarantined individuals make no contacts, and infectious individuals of subpopulation $\alpha \in \{\mathrm n, \mathrm v\}$ avoid each potentially infectious contact with probability $\sigma_\alpha$ (their responsibility level). A contact between S and I transmits with probability $\lambda$, reduced to $\lambda(1-\gamma_{\mathrm t})$ if the susceptible is vaccinated. A new infection is severe (goes directly to Q) with probability $p_{\mathrm q}$, reduced to $p_{\mathrm q}(1-\gamma_{\mathrm q})$ for vaccinated individuals. Infected individuals recover to S at rate $\beta$, and free testing moves I to Q at rate $\tau$ (the control).

**Theorem (epidemic threshold).** In the mean-field approximation and the large-population limit $n \to \infty$, let

$$\xi := (1-p_{\mathrm q})(1-\sigma_{\mathrm n})\bigl[\theta + (1-\theta)(1-v)\bigr] + (1-\gamma_{\mathrm t})\bigl[1 - p_{\mathrm q}(1-\gamma_{\mathrm q})\bigr](1-\sigma_{\mathrm v})\bigl[\theta + (1-\theta)v\bigr],$$

$$\bar\tau := \lambda\xi - \beta + \lambda\sqrt{\xi^2 - 4\theta(1-\gamma_{\mathrm t})(1-p_{\mathrm q})\bigl[1 - p_{\mathrm q}(1-\gamma_{\mathrm q})\bigr](1-\sigma_{\mathrm n})(1-\sigma_{\mathrm v})}.$$

If the testing rate satisfies $\tau > \bar\tau$, the disease-free equilibrium is locally asymptotically stable. In particular, no testing is needed if $\beta$ exceeds $\lambda\xi$ plus the square-root term. Without homophily ($\theta = 0$) the threshold reduces to

$$\tau^* = 2\lambda(1-p_{\mathrm q})(1-v)(1-\sigma_{\mathrm n}) + 2\lambda(1-\gamma_{\mathrm t})\,v\,\bigl[1 - p_{\mathrm q}(1-\gamma_{\mathrm q})\bigr](1-\sigma_{\mathrm v}) - \beta .$$

The threshold separates the effect of vaccines on transmission ($\gamma_{\mathrm t}$) from their effect on severity ($\gamma_{\mathrm q}$). A vaccine that mainly prevents severe illness increases the share of mild, untested infectious vaccinated individuals and can raise the testing effort needed. Polarization $\theta > 0$ concentrates transmission in the non-vaccinated group.

## Expansion

A susceptible individual's infection rate is the sum of two Poisson streams: contacts it initiates and contacts initiated by others. This gives the factor $2\lambda$ and a dependence on the infectious fractions in its own and the other subpopulation, weighted by $\theta + (1-\theta)\times$(subpopulation share) or $(1-\theta)\times$(share). Linearizing the large-$n$ mean-field equations for the infectious fractions $(y_{\mathrm n,\mathrm i}, y_{\mathrm v,\mathrm i})$ at the disease-free state gives a $2\times2$ matrix with diagonal entries $2\lambda(\cdot) - (\beta + \tau)$. Its largest eigenvalue is $\tfrac12\bigl(\operatorname{tr} + \sqrt{\operatorname{tr}^2 - 4\det}\bigr)$. Requiring it to be negative yields the quadratic-formula threshold $\bar\tau$, and the determinant term vanishes when $\theta = 0$.

## Sources

- Kathinka Frieswijk, Lorenzo Zino, Ming Cao, "A Polarized Temporal Network Model to Study the Spread of Recurrent Epidemic Diseases in a Partially Vaccinated Population", arXiv (2022). Section 3 (model: network formation, contagion, recovery, testing), Section 4: Propositions 2–4, Theorem 1, the following remark and corollary. <https://doi.org/10.48550/arXiv.2209.08045>. Published version: IEEE Transactions on Network Science and Engineering 10(6) (2023), <https://doi.org/10.1109/tnse.2023.3272472>; locators above refer to the arXiv version.
