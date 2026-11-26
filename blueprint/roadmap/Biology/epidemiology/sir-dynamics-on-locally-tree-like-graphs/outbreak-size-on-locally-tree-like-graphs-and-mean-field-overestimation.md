# Outbreak size on locally tree-like graphs and mean-field overestimation

**Setting.** As in the exact ODE limit: SIR (or SEIR) with infection rate $\beta_t$ and recovery rate $\rho_t$ on Erdős–Rényi or configuration-model graphs with limiting degree law $\theta$, size-biased law $\hat\theta$, moment generating function $M_\zeta(x) = \sum_k \zeta(k)e^{kx}$, and initial susceptible fraction $s_0 \in (0,1)$; $(f_S, f_I, F_I)$ solves the limiting ODE.

**Theorem (final size).**

$$\lim_{n\to\infty}\lim_{t\to\infty} s^{G_n}(t) = \lim_{t\to\infty} s^{(\infty)}(t) = s_0\,M_\theta(-F_\infty), \qquad F_\infty = \int_0^\infty \beta_u f_I(u)\,du < \infty,$$

where $F_\infty$ satisfies

$$F_\infty + \log M_{\hat\theta}(-F_\infty) - \log\left(1 - e^{F_\infty}\int_0^\infty e^{-\int_0^u \beta_\tau f_I(\tau)d\tau}\rho_u f_I(u)\,du\right) + \log s_0 = 0.$$

If $\rho_t / \beta_t \equiv r \in (0,\infty)$, this reduces to

$$F_\infty + \log M_{\hat\theta}(-F_\infty) - \log\big(1 + r(1 - e^{F_\infty})\big) + \log s_0 = 0,$$

which has a unique strictly positive solution. For constant infection and recovery rates, the SIR and SEIR processes with the same initial condition have the same outbreak size (the latent period does not change it); with time-varying rates their outbreak sizes can differ substantially.

**Corollary (random regular graphs).** For uniform $\kappa$-regular graphs ($\kappa \ge 2$) and $\rho_t/\beta_t \equiv r$, the final susceptible fraction is the unique root $\sigma_\kappa \in (0,s_0)$ of

$$z^{(\kappa-2)/\kappa}s_0^{2/\kappa} - (1+r) + r\,z^{-1/\kappa}s_0^{1/\kappa} = 0;$$

in particular $\sigma_2 = s_0 / (1 + r(1-s_0))^2$.

**Proposition (mean field overestimates).** The mean-field SIR model $\dot{\hat s} = -\beta\kappa \hat s\hat i$, $\dot{\hat i} = \beta\kappa\hat s\hat i - \rho\hat i$ with the same $s_0$ and ratio $r$ has final susceptible fraction $\hat\sigma_\kappa$ solving $s_0 e^{\kappa(z-1)/r} = z$, and $\hat\sigma_\kappa < \sigma_\kappa$ for every $\kappa \ge 2$: the mean-field prediction always overestimates the outbreak size on random regular graphs.

## Depends on

- [Exact ODE limit of SIR and SEIR epidemics on sparse locally tree-like graphs](exact-ode-limit-of-sir-and-seir-epidemics-on-locally-tree-like-graphs.md)

## Expansion

Integrating the limiting ODE to $t = \infty$ gives the implicit equation for the total per-edge infection pressure $F_\infty$; with a constant ratio $r$ the integral term becomes explicit. On a $\kappa$-regular tree, $M_\theta(x) = e^{\kappa x}$ and $M_{\hat\theta}(x) = e^{(\kappa-1)x}$, so substituting $z = s_0 e^{-\kappa F_\infty}$ turns the equation into $\phi_\kappa(z) = 0$. The mean-field model ignores that an infected vertex cannot reinfect the neighbor that infected it and that infections deplete local susceptibles, so it overestimates spread. With constant rates the exposed stage delays but does not alter the probability that infection passes along an edge, which gives the SEIR identity; with time-varying rates the delay shifts infections into periods with different $\beta_t/\rho_t$, which breaks it.

## Sources

- J. Cocomello, K. Ramanan, "Exact description of limiting SIR and SEIR dynamics on locally tree-like graphs", arXiv:2309.08829 (2023), Theorems 3.1 and 3.5, Corollary 3.6, Proposition 3.7 and the mean-field comparison (Section 3), <https://doi.org/10.48550/arXiv.2309.08829>.
