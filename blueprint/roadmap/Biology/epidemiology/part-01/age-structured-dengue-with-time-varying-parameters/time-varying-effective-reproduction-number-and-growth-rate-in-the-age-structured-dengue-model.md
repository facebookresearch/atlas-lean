# Time-varying effective reproduction number and growth rate in the age-structured dengue model

**Setting.** In the age-structured dengue model with time- and age-dependent rates, let $i_m(t)$ be the proportion of infected mosquitoes, $s_m(t)$ the susceptible proportion, $\mathcal{N}_m(t)$ and $\Lambda_m(t)$ the mosquito population and recruitment, $p(t,\zeta)$ the host age distribution, $\beta_m, \beta_h$ the transmission rates, $s + \sigma v$ the effective host susceptibility (susceptibles plus vaccinees weighted by relative susceptibility $\sigma$), and $F(t,\eta,\zeta)$ the probability that a host infected at age $\eta$ is still infectious at age $\zeta$. Infections started at $t^0$. Define the instantaneous growth rate $r_t = \frac{d}{dt}\log i_m(t)$, so that $i_m(t - u) = i_m(t)e^{-\int_{t-u}^tr_\tau\,d\tau}$.

**Time-varying Lotka equation.** Integrating the infected-host equations along characteristics and substituting into the mosquito equation gives $1 = \mathcal{L}(t, r_t)$ with

$$
\mathcal{L}(t, r_t) = \frac{\mathcal{N}_m(t)s_m(t)}{r_t\mathcal{N}_m(t) + \Lambda_m(t)}\int_0^\infty\beta_m(t,\zeta)p(t,\zeta)\int_{\max\{0,\,t^0+\zeta-t\}}^\zeta\beta_h(\eta+t-\zeta,\eta)\,\big[s+\sigma v\big](\eta+t-\zeta,\eta)\,F(t,\eta,\zeta)\,e^{-\int_{\eta+t-\zeta}^tr_\tau\,d\tau}\,d\eta\,d\zeta.
$$

**Definition.** The time-varying effective reproduction number is the value at zero growth,

$$
\mathcal{R}_f(t) = \frac{\mathcal{N}_m(t)s_m(t)}{\Lambda_m(t)}\int_0^\infty\beta_m(t,\zeta)p(t,\zeta)\int_{\max\{0,\,t^0+\zeta-t\}}^\zeta\beta_h(\eta+t-\zeta,\eta)\,\big[s+\sigma v\big](\eta+t-\zeta,\eta)\,F(t,\eta,\zeta)\,d\eta\,d\zeta,
$$

the expected number of secondary infections at time $t$. It reduces to the basic effective reproduction number at the disease-free state, and it falls as host and mosquito susceptibles deplete or vaccination proceeds.

**Proposition (growth rate relation).** If $i_m(t - u)/i_m(t)$ is replaced by its first-order expansion $1 - r_tu$ over the short infection ages $u = \zeta - \eta$, then

$$
r_t = \frac{\Lambda_m(t)}{\mathcal{N}_m(t)\,(1 + \mathcal{K}_t)}\big(\mathcal{R}_f(t) - 1\big), \qquad \mathcal{K}_t = \int_0^\infty s_m(t)\beta_m(t,\zeta)p(t,\zeta)\int_{\max\{0,\,t^0+\zeta-t\}}^\zeta\beta_h(\eta+t-\zeta,\eta)(\zeta-\eta)\,\big[s+\sigma v\big](\eta+t-\zeta,\eta)\,F(t,\eta,\zeta)\,d\eta\,d\zeta.
$$

So incidence in mosquitoes increases, is flat, or decreases at time $t$ exactly as $\mathcal{R}_f(t)$ is above, at, or below $1$, and $\mathcal{R}_f(t) = 1 + r_t/\gamma(t)$ with $\gamma(t) = \Lambda_m(t)/(\mathcal{N}_m(t)(1 + \mathcal{K}_t))$. This is the form $r_t = \gamma(t)(\mathcal{R}_f(t) - 1)$ familiar from discrete-time renewal models, and it lets $\mathcal{R}_f(t)$ be estimated from surveillance growth rates.

## Depends on

- [Basic effective reproduction number of the age-structured dengue model via the Lotka equation](basic-effective-reproduction-number-of-the-age-structured-dengue-model-via-the-lotka-equation.md)
- [Euler–Lotka equation for the reproductive number](../../euler-lotka-equation-and-the-reproduction-number/renewal-exp-iff-reproduction-number.md)

## Expansion

Write the mosquito equation as $\frac{1}{i_m}\frac{di_m}{dt} = \frac{\Lambda_m}{\mathcal{N}_m}\big[\frac{\mathcal{N}_m}{\Lambda_m}\int\int s_m\beta_m p\,\beta_h[s+\sigma v]F\,\frac{i_m(t-(\zeta-\eta))}{i_m(t)}\,d\eta\,d\zeta - 1\big]$. With the linear approximation $i_m(t-u)/i_m(t) \approx 1 - r_tu$, the double integral splits into $\frac{\Lambda_m}{\mathcal{N}_m}\mathcal{R}_f(t)$ minus $r_t$ times the infection-age-weighted integral $\frac{\Lambda_m}{\mathcal{N}_m}\mathcal{K}_t$. Hence $r_t = \frac{\Lambda_m}{\mathcal{N}_m}(\mathcal{R}_f(t) - 1) - r_t\mathcal{K}_t$, and solving for $r_t$ gives the relation. $\mathcal{K}_t$ is the mean infection age weighted by infectiousness, so the correction $1 + \mathcal{K}_t$ plays the role of a mean generation time. The approximation needs the infection age and the mosquito lifespan to be short relative to the time scale on which $r_t$ changes.

## Sources

- Ihtisham Ul Haq and Serge Richard, "Age-structured model of dengue transmission dynamics with time-varying parameters, and its application to Brazil", arXiv:2511.16179 (2025), Section 8 (time-varying Lotka equation and the definition of the time-varying effective reproduction number), Section 9 (relation between the instantaneous growth rate and the time-varying effective reproduction number), <https://doi.org/10.48550/arXiv.2511.16179>. Published version: Nonlinear Science 7 (2026), article 100133, <https://doi.org/10.1016/j.nls.2026.100133>; locators above refer to the arXiv version.
