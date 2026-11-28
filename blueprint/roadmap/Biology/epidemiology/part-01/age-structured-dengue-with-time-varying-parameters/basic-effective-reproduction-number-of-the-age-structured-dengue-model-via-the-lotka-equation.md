# Basic effective reproduction number of the age-structured dengue model via the Lotka equation

**Model.** Hosts of age $\zeta \ge 0$ at time $t$ are described by proportions $s, v, i_a, i_s, h, r$ (susceptible, vaccinated, asymptomatic, symptomatic, hospitalised, recovered) of the age density $p(t,\zeta)$. Mosquitoes are described by the susceptible and infected proportions $s_m, i_m$ of a population $\mathcal{N}_m(t)$ with recruitment $\Lambda_m(t)$. With vaccination rate $\alpha$, relative susceptibility $\sigma$ of vaccinees, symptomatic fraction $f$, recovery rates $\kappa_a, \kappa_s, \kappa_H$, hospitalisation rate $\delta$, hospital death rate $\mu_H$, and mosquito-to-host and host-to-mosquito transmission rates $\beta_h, \beta_m$ (all functions of $(t,\zeta)$), the infected hosts satisfy

$$
\Big(\partial_t + \partial_\zeta\Big)i_a = (1-f)\beta_h\,i_m(t)\,(s + \sigma v) - (\kappa_a + g)i_a, \qquad \Big(\partial_t + \partial_\zeta\Big)i_s = f\beta_h\,i_m(t)\,(s + \sigma v) - (\kappa_s + \delta + g)i_s,
$$

with $g = -\mu_Hh$, and the infected mosquitoes satisfy

$$
\frac{di_m}{dt} = s_m(t)\int_0^\infty\beta_m(t,\zeta)p(t,\zeta)\big(i_s(t,\zeta) + i_a(t,\zeta)\big)\,d\zeta - \frac{\Lambda_m(t)}{\mathcal{N}_m(t)}\,i_m(t).
$$

The susceptible and vaccinated equations, boundary conditions $s(t,0) = 1$ and zero for the other classes, and the $h, r, s_m$ equations complete the system. At the disease-free state at time $t^0$ the profiles $s^0(\zeta) = e^{-\int_0^\zeta\alpha}$ and $v^0 = 1 - s^0$ hold (with vaccination the only transition), and $p^0$ is the host age distribution.

**Infectious-period kernel.** The probability that a host infected at age $\eta$ is still infectious at age $\zeta \ge \eta$ is

$$
F(\eta,\zeta) = (1 - f(t^0,\eta))\,e^{-\int_\eta^\zeta\kappa_a(t^0,\xi)\,d\xi} + f(t^0,\eta)\,e^{-\int_\eta^\zeta[\kappa_s(t^0,\xi) + \delta(t^0,\xi)]\,d\xi}.
$$

**Lotka equation and reproduction number.** Linearising at the disease-free state with parameters frozen at $t^0$ and seeking $i_m(t) \propto e^{\lambda(t-t^0)}$ leads to the characteristic equation $L(\lambda) = 1$, where

$$
L(\lambda) = \frac{\mathcal{N}_m^0}{\lambda\mathcal{N}_m^0 + \Lambda_m(t^0)}\int_0^\infty\beta_m(t^0,\zeta)p^0(\zeta)\int_0^\zeta\beta_h(t^0,\eta)\big(s^0(\eta) + \sigma(t^0,\eta)v^0(\eta)\big)F(\eta,\zeta)e^{-\lambda(\zeta-\eta)}\,d\eta\,d\zeta.
$$

The **basic effective reproduction number** is $\mathcal{R}_{f,0} = L(0)$:

$$
\mathcal{R}_{f,0} = \frac{\mathcal{N}_m^0}{\Lambda_m(t^0)}\int_0^\infty\beta_m(t^0,\zeta)p^0(\zeta)\int_0^\zeta\beta_h(t^0,\eta)\big(s^0(\eta) + \sigma(t^0,\eta)v^0(\eta)\big)F(\eta,\zeta)\,d\eta\,d\zeta.
$$

The factors are the mean mosquito lifetime $\mathcal{N}_m^0/\Lambda_m(t^0)$, the effective susceptibility $s^0 + \sigma v^0$ reduced by vaccination, the infectious-survival kernel $F$, and the age distribution $p^0$.

**Theorem.** The disease-free equilibrium is locally asymptotically stable if $\mathcal{R}_{f,0} < 1$ and unstable if $\mathcal{R}_{f,0} > 1$.

**Age-independent check.** With constant parameters, no vaccination ($\sigma = 0$ in the infected block) and no age structure, the next-generation matrix has eigenvalues $0$ and $\pm\sqrt{\frac{\beta_m\beta_hS_m^0S^0}{\mu_m\mathcal{N}_m^0\mathcal{N}_h^0}\left(\frac{f}{\kappa_s+\delta+\mu_h} + \frac{1-f}{\kappa_a+\mu_h}\right)}$. The positive root is the next-generation $R_0$, a square root over the host-to-vector and vector-to-host generations. $\mathcal{R}_{f,0}$ is instead the product of the two generations, with no square root, so the two thresholds agree at $1$ but differ away from it.

## Depends on

- [Euler–Lotka equation for the reproductive number](../../euler-lotka-equation-and-the-reproduction-number/renewal-exp-iff-reproduction-number.md)
- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

Integrating the linearised infected-host equations along characteristics expresses $i_a + i_s$ at age $\zeta$ as an integral over the infection age $\eta$ of $\beta_h(s^0 + \sigma v^0)F(\eta,\zeta)i_m(t - (\zeta - \eta))$. Substituting into the $i_m$ equation gives a renewal equation for $i_m$, and an exponential ansatz turns it into $L(\lambda) = 1$. Because $L$ is strictly decreasing in real $\lambda$ with $L(\lambda) \to 0$ as $\lambda \to \infty$, the dominant real root is positive exactly when $L(0) > 1$, and complex roots have real part below the real root. This gives the stability statement.

## Sources

- Ihtisham Ul Haq and Serge Richard, "Age-structured model of dengue transmission dynamics with time-varying parameters, and its application to Brazil", arXiv:2511.16179 (2025), Sections 2–4 (model, rescaling, disease-free state and Lemma 4.1), Section 5 (Lotka equation and basic effective reproduction number), Section 6 (Lemma 6.1, next-generation comparison), Section 7 (Theorem 7.1), <https://doi.org/10.48550/arXiv.2511.16179>. Published version: Nonlinear Science 7 (2026), article 100133, <https://doi.org/10.1016/j.nls.2026.100133>; locators above refer to the arXiv version.
