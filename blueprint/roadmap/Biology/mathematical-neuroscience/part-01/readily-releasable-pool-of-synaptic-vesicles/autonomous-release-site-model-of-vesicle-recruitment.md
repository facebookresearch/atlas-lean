# Autonomous release-site model of vesicle recruitment

**Model.** A presynaptic terminal has a fixed number $RRP_0$ of autonomous release sites. At time $t$, site $i$ is either full ($F_{i,t} = 1$, holding a readily releasable vesicle) or empty ($E_{i,t} = 1 - F_{i,t}$). An empty site recruits a vesicle at unitary rate $\alpha_{i,t} \ge 0$ and a full site releases at unitary rate $\beta_{i,t} \ge 0$ (during stimulation at frequency $\nu$, $\beta$ is the release probability per action potential times $\nu$); both may vary across sites and in time, which covers sequential priming (release probability increasing with time since recruitment) and parallel site types. With $RRP_t = \sum_i F_{i,t}$ occupied sites,

$$\frac{dRRP_t}{dt} = \hat\alpha_t\,(RRP_0 - RRP_t) - \hat\beta_t\, RRP_t, \qquad \hat\alpha_t = \frac{\sum_i \alpha_{i,t} E_{i,t}}{\sum_i E_{i,t}}, \quad \hat\beta_t = \frac{\sum_i \beta_{i,t} F_{i,t}}{\sum_i F_{i,t}},$$

where $\hat\alpha_t$ is the mean recruitment rate over empty sites and $\hat\beta_t$ the mean release rate over full sites. Unitary rates are per site; bulk rates are $\hat\alpha_t (RRP_0 - RRP_t)$ and $\hat\beta_t RRP_t$.

**Proposition.**

1. *(Cumulative release.)* Over $[0, t]$ the number of vesicles released is

    $$\int_0^t \hat\beta_s RRP_s\, ds = \big(RRP_0^{\mathrm{init}} - RRP_t\big) + \int_0^t \hat\alpha_s (RRP_0 - RRP_s)\, ds,$$

    the depletion of the pool plus the cumulative recruitment; starting from rest ($RRP = RRP_0$), cumulative release exceeds $RRP_0$ by the cumulative recruitment minus $RRP_t$, that is, by exactly the cumulative recruitment once the pool is empty ($RRP_t = 0$).

2. *(Steady state.)* If stimulation at frequency $\nu$ reaches a steady state with release $R_{ss}$ per action potential and constant $\hat\alpha = \hat\alpha_{\mathrm{fixed}}$, then $R_{ss}\,\nu = \hat\alpha_{\mathrm{fixed}}(RRP_0 - RRP_{ss})$, so

    $$RRP_0 = \frac{R_{ss}\,\nu}{\hat\alpha_{\mathrm{fixed}}} + RRP_{ss},$$

    which reduces to $RRP_0 = R_{ss}\nu/\hat\alpha_{\mathrm{fixed}}$ when heavy stimulation empties the pool ($RRP_{ss} \approx 0$).

3. *(Saturation.)* Bulk recruitment is proportional to the unitary rate only when the pool is empty; with constant $\hat\alpha$, recovery from a depleted pool during rest is exponential with rate $\hat\alpha$.

## Expansion

Summing the two-state transitions over sites gives $\frac{d}{dt}RRP_t = \sum_i \alpha_{i,t} E_{i,t} - \sum_i \beta_{i,t} F_{i,t}$, and the mean rates are defined so that this equals the displayed equation; sequential models with discrete priming states fit by averaging $\beta$ over all full substates. Integrating gives the cumulative-release identity, and setting the derivative to zero gives the steady-state relation. Because both sides of the steady-state identity are measurable (release per spike and frequency) once $\hat\alpha$ is fixed, $\hat\alpha_{\mathrm{fixed}}$ and $RRP_0$ can be fitted by requiring the same $RRP_0$ from different stimulation protocols; at the calyx of Held this gives $\hat\alpha_{\mathrm{fixed}} \approx 4.7\,\mathrm{s}^{-1}$ for both $300$ Hz trains and $100 \to 300$ Hz frequency jumps, while the excess release in frequency-jump trials requires a flow-through pool of low-release-probability vesicles or activity-dependent acceleration of recruitment.

## Sources

- K. Mahfooz, M. Singh, R. Renden and J. F. Wesseling, "A well-defined readily releasable pool with fixed capacity for storing vesicles at calyx of Held", PLoS Computational Biology 12 (2016), e1004855, Results (Eq. 1, Fig. 6) and Methods (Lemma 2), <https://doi.org/10.1371/journal.pcbi.1004855>, PMCID: PMC4818018.
