# Backward equations for a birth–death process with rate shifts

**Model.** Lineages speciate and go extinct according to a birth–death process whose parameters $(\lambda_i, \mu_i)$ are those of the rate regime $i$ the lineage belongs to; any lineage moves to a new regime, drawn from a distribution over parameter values, at rate $\eta \ge 0$. Measure time $t$ backward from the present. For a point on an observed branch in regime $i$ at time $t$, let $D_i(t)$ be the probability that the lineage gives rise exactly to the observed descendant subtree with no rate shift on it, and $E_i(t)$ the probability that a lineage starting in regime $i$ at time $t$ leaves no sampled descendant. Then

$$\frac{dD_i}{dt} = -(\lambda_i + \mu_i + \eta)\,D_i(t) + 2\lambda_i D_i(t) E_i(t),$$

$$\frac{dE_i}{dt} = \mu_i - (\lambda_i + \mu_i + \eta)\,E_i(t) + \lambda_i E_i(t)^2 + \eta\, \Phi(t, \eta),$$

where $\Phi(t,\eta)$ is the probability that a lineage which shifts at time $t$ to a new regime is not sampled. At a tip, $E_i(0) = 1 - f$ and $D_i(0) = f$ for sampling fraction $f$; at an observed speciation node the $D$ values of the two daughters are multiplied by $\lambda_i$.

**Proposition (constant rates).** If $\eta = 0$ and sampling is complete ($f = 1$), with $\lambda \ne \mu$,

$$E(t) = \frac{\mu\big(1 - e^{-(\lambda - \mu)t}\big)}{\lambda - \mu\, e^{-(\lambda - \mu)t}},$$

the probability that a single lineage alive at time $t$ before the present has no living descendants.

## Expansion

Condition on the first event in a short interval $dt$ (backward from $t$): with probability $\mu\,dt$ the lineage goes extinct, with probability $\lambda\,dt$ it splits and both daughters must die out ($E^2$), with probability $\eta\,dt$ it shifts regime, and otherwise nothing happens. This yields the Riccati equation for $E$; the equation for $D$ follows the same way, except that an unobserved split is allowed only if one daughter leaves no sampled descendant (factor $2\lambda E$) and a shift on an observed branch would contradict the mapped history. For $\eta = 0$ the Riccati equation $E' = \mu - (\lambda + \mu)E + \lambda E^2 = (1 - E)(\mu - \lambda E)$ has fixed points $1$ and $\mu/\lambda$, and separation of variables with $E(0) = 0$ gives the displayed formula, which tends to $\min(1, \mu/\lambda)$ as $t \to \infty$. Published multi-rate models such as MEDUSA, split-BiSSE and BAMM set $\eta\Phi = 0$ in the $E$ equation, ignoring shifts on unobserved lineages; the source shows this matters only at shift frequencies 100–1000 times larger than those estimated from the empirical trees examined.

## Sources

- D. L. Rabosky, J. S. Mitchell and J. Chang, *Is BAMM flawed? Theoretical and practical concerns in the analysis of multi-rate diversification models*, Systematic Biology (2017). <https://doi.org/10.1093/sysbio/syx037> (PMCID: PMC5790138). Section "Likelihoods of Rate-Shift Models", Equations (1)–(3), Table 2.
- W. P. Maddison, P. E. Midford and S. P. Otto, *Estimating a binary character's effect on speciation and extinction*, Systematic Biology (2007).
