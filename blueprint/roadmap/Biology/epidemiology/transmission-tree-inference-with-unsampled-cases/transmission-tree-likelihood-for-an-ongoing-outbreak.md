# Transmission-tree likelihood for an ongoing outbreak

Keep the branching process of the
[partially sampled transmission tree](likelihood-of-a-partially-sampled-transmission-tree.md), but
stop observation at a known time $T_{\mathrm{obs}}$, so cases infected late have less time to be
sampled. A case infected at time $t$ is sampled with probability

$$\pi_t = \pi \int_0^{T_{\mathrm{obs}} - t} \sigma(\tau)\, d\tau ,$$

and its exclusion probability $\omega_t$ satisfies $\omega_t = 1$ for $t \ge T_{\mathrm{obs}}$ and

$$\omega_t = (1 - \pi_t)\, G(\bar\omega_t), \qquad
\bar\omega_t = \int_0^\infty \gamma(\tau)\, \omega_{t+\tau}\, d\tau ,$$

with $\omega_t \to \omega_\ast$ as $t \to -\infty$. With the time-dependent modified offspring
function $\alpha_t(d) = \sum_{k \ge d}\binom{k}{d}\alpha(k)\,\bar\omega_t^{\,k-d}$, the probability
of a transmission tree is

$$P(T \mid \theta) = \prod_{i=1}^{n} \Big[ \big(1 - \pi_{t_i^{\mathrm{inf}}}\big)^{1-s_i}
\big(\pi_{t_i^{\mathrm{inf}}}\, \sigma_t(t_i^{\mathrm{sam}} - t_i^{\mathrm{inf}})\big)^{s_i}\,
\alpha_{t_i^{\mathrm{inf}}}(d_i) \prod_{j=1}^{d_i} \gamma_t(t_j^{\mathrm{inf}} - t_i^{\mathrm{inf}}) \Big],$$

where $\sigma_t$ and $\gamma_t$ are $\sigma$ and $\gamma$ truncated at $\tau = T_{\mathrm{obs}} - t$.

## Depends on

- [Likelihood of a partially sampled transmission tree](likelihood-of-a-partially-sampled-transmission-tree.md)

## Expansion

Right-censoring at $T_{\mathrm{obs}}$ makes sampling depend on infection time: a case can only be
sampled if its sampling delay ends before observation stops, which gives $\pi_t$. An offspring of
a case infected at $t$ is itself infected at $t + \tau$ with $\tau \sim \gamma$ and is excluded with
probability $\omega_{t+\tau}$; averaging over $\tau$ gives $\bar\omega_t$, and the same
generating-function argument as in the finished case gives an integral equation, solved
numerically backwards from $\omega_t = 1$ for $t \ge T_{\mathrm{obs}}$. The recursive
decomposition over subtrees is unchanged, with $\omega_\ast$ replaced by $\bar\omega_t$ evaluated
at each case's infection time.

## Sources

- X. Didelot, C. Fraser, J. Gardy, C. Colijn, "Genomic infectious disease epidemiology in
  partially sampled and ongoing outbreaks", Molecular Biology and Evolution 34 (2017) 997-1007,
  "Ongoing Outbreak Scenario", Eqs. (8)-(11), <https://doi.org/10.1093/molbev/msw275>
  (PMC5850352).
