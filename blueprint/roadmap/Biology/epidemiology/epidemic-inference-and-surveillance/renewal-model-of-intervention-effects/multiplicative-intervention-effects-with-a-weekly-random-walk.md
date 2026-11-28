# Multiplicative intervention effects with a weekly random walk

**Model.** For locations $l$ and days $t$, let $x_{i,t,l} \in \{0,1\}$ indicate that non-pharmaceutical intervention $i \in \{1,\dots,I\}$ is active. The instantaneous reproduction number is

$$R_{t,l} = \tilde R_{0,l} \prod_{i = 1}^{I} \exp(-\beta_i x_{i,t,l})\; \exp(z_{t,l}),$$

where $\tilde R_{0,l} > 0$ is the reproduction number at the start of the period had no intervention been active, $\beta_i \in \mathbb{R}$ is an effect shared across locations, and $z_{t,l}$ is a weekly random walk: $z_{t,l} = 0$ for $t \le 13$, and for $t \ge 14$, $z_{t,l} = z_{t-1,l} + \varepsilon_{\lfloor (t - 14)/7 \rfloor, l}$ if $t \equiv 0 \pmod 7$ and $z_{t,l} = z_{t-1,l}$ otherwise, with $\varepsilon_{j,l} \sim \mathcal{N}(0, \sigma_R^2)$ independent. Expected infections follow the discrete renewal equation

$$\bar N_{t,l} = R_{t,l} \sum_{\tau = 1}^{32} \bar N_{t - \tau, l}\, \pi_{\mathrm{GI}}[\tau]$$

for a generation-interval distribution $\pi_{\mathrm{GI}}$, realized infections are $N_{t,l} = \mathrm{softplus}(\bar N_{t,l} + \epsilon_{t,l})$ with $\epsilon_{t,l} \sim \mathcal{N}(0, 5^2)$, and expected cases and deaths are discrete convolutions of $N_{t,l}$ with reporting and death delay distributions.

**Proposition.**

1. Activating intervention $i$ while everything else is held fixed multiplies $R_{t,l}$ by $e^{-\beta_i}$, a reduction of $1 - e^{-\beta_i}$ that does not depend on the location, the time or the other active interventions; a set $\mathcal{S}$ of interventions reduces $R_{t,l}$ by $1 - \exp(-\sum_{i \in \mathcal{S}} \beta_i)$.
2. $\log R_{t,l}$ is linear in the indicators, and conditionally on $\sigma_R$ the latent term $z_{t,l}$ is piecewise constant over weeks with $\mathrm{Var}(z_{t,l}) = \sigma_R^2\, \#\{7 j \le t : j \ge 2\}$, so unexplained changes in transmission accumulate only at week boundaries.
3. If $\bar N$ grows at a constant exponential rate $r$, the renewal equation forces $R_{t,l} = 1/\sum_\tau e^{-r\tau}\pi_{\mathrm{GI}}[\tau]$.

## Depends on

- [Case reproduction number as a smoothed instantaneous reproduction number](../case-and-instantaneous-reproduction-numbers/case-reproduction-number-as-a-smoothed-instantaneous-reproduction-number.md)
- [Reproductive number from growth rate and generation interval](../../euler-lotka-equation-and-the-reproduction-number/reproduction-number.md)

## Expansion

Item 1 is immediate from the product form: switching $x_{i,t,l}$ from $0$ to $1$ multiplies by $e^{-\beta_i}$, and exponentials of sums factor. For item 2, $z_{t,l}$ changes only on days $t \ge 14$ divisible by $7$, and each change adds an independent $\mathcal{N}(0,\sigma_R^2)$ increment. Item 3 follows by substituting $\bar N_{t} = C e^{rt}$ into the renewal equation. The random walk absorbs unrecorded interventions and changes in adherence, so intervention effects are identified from the coincidence of reported changes in transmission with recorded intervention dates across many locations; the source places an asymmetric Laplace shrinkage prior on $\beta_i$ with 80% of its mass on positive effects.

## Sources

- M. Sharma, S. Mindermann, C. Rogers-Smith, G. Leech, B. Snodin, J. Ahuja, J. B. Sandbrink et al., *Understanding the effectiveness of government interventions against the resurgence of COVID-19 in Europe*, Nature Communications (2021). <https://doi.org/10.1038/s41467-021-26013-4> (PMCID: PMC8492703). Methods: "Reproduction number", "Infection process".
