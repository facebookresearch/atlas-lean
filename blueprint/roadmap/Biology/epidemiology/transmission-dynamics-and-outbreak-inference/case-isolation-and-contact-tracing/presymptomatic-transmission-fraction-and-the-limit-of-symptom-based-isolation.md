# Presymptomatic transmission fraction and the limit of symptom-based isolation

**Setting.** In the [branching-process model of case isolation and contact tracing](branching-process-model-of-case-isolation-and-contact-tracing.md), let the incubation period $T > 0$ have any law (a Weibull law in the source) and, given $T$, let the serial interval be skew-normal with location $T$, scale $\omega > 0$ and shape $\alpha \in \mathbb{R}$:

$$S \mid T \sim \mathrm{SN}(\xi = T,\ \omega,\ \alpha).$$

The *presymptomatic transmission fraction* is $\theta = \Pr(S < T)$.

**Proposition 1 (closed form).** $\theta$ does not depend on the law of $T$ or on $\omega$:

$$\theta = \frac12 - \frac{1}{\pi}\arctan \alpha, \qquad \text{equivalently} \qquad \alpha = \cot(\pi \theta) \quad (0 < \theta < 1).$$

For $\theta = 0.15$ and $\theta = 0.30$ this gives $\alpha \approx 1.96$ and $\alpha \approx 0.73$; $\theta < 0.01$ requires $\alpha > \cot(0.01\pi) \approx 31.8$.

**Proposition 2 (isolation floor).** Suppose every case is symptomatic and there is no quarantine of asymptomatic contacts, so that $\tau_i - t_i \ge T_i$ for every case, whatever $\rho$ and $D$. Then

$$R_{\mathrm{eff}} \ge R_0\, \theta .$$

In particular, if $R_0 \theta > 1$, no combination of tracing probability and isolation delay makes the controlled branching process subcritical.

## Depends on

- [Branching-process model of case isolation and contact tracing](branching-process-model-of-case-isolation-and-contact-tracing.md)

## Proof sketch

For $Z \sim \mathrm{SN}(0,1,\alpha)$ the distribution function at $0$ is $\Phi(0) - 2\,\mathcal{T}(0,\alpha) = \tfrac12 - \tfrac{1}{\pi}\arctan\alpha$, where $\mathcal{T}$ is Owen's function. Since $(S - T)/\omega \mid T \sim \mathrm{SN}(0,1,\alpha)$, $\Pr(S < T \mid T) = \Pr(Z < 0)$ is constant, which proves Proposition 1. For Proposition 2, $\tau_i - t_i \ge T_i$ gives $q(T_i, \tau_i - t_i) \ge \Pr(S < T_i \mid T_i) = \theta$, so $R_{\mathrm{eff}} = R_0\,\mathbb{E}[q] \ge R_0\theta$. With $R_0 = 3.5$ and $\theta = 0.3$ the floor is $1.05$, consistent with the source's finding that high presymptomatic transmission defeats isolation and tracing at large $R_0$. The source correlates $S$ and $T$ in exactly this way, using scale $2$ days and choosing the shape so that less than 1%, 15% or 30% of transmission precedes symptom onset.

## Sources

- J. Hellewell, S. Abbott, A. Gimma, N. I. Bosse, C. I. Jarvis, T. W. Russell, J. D. Munday, A. J. Kucharski, W. J. Edmunds, CMMID COVID-19 working group, S. Funk and R. M. Eggo, *Feasibility of controlling COVID-19 outbreaks by isolation of cases and contacts*, Lancet Glob. Health 8 (2020), e488–e496. <https://doi.org/10.1016/S2214-109X(20)30074-7> (PMCID: PMC7097845). Methods (model description, table of parameters, Figures 1–2).
- A. Azzalini, *A class of distributions which includes the normal ones*, Scand. J. Statist. 12 (1985), 171–178.
- C. Fraser, S. Riley, R. M. Anderson and N. M. Ferguson, *Factors that make an infectious disease outbreak controllable*, Proc. Natl. Acad. Sci. USA 101 (2004), 6146–6151. <https://doi.org/10.1073/pnas.0307506101>
