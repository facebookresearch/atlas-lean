# Reproduction number and bifurcation in an age- and infection-age-structured malaria model

**Model.** Humans are susceptible $S_h(t,a)$, infected $I_h(t,a,\tau)$ (age $a$, time since infection $\tau$) or recovered $R_h(t,a,\eta)$ (time since recovery $\eta$); mosquitoes are susceptible $S_m(t,a)$ or infected $I_m(t,a,\tau)$. Humans and mosquitoes are recruited at rates $\Lambda_h, \Lambda_m$ and die at age-dependent rates $\mu_h(a), \mu_m(a)$; infected humans recover at rate $\gamma_h(a,\tau)$ and die of the disease at rate $\nu_h(a,\tau)$, infected mosquitoes die of infection at rate $\nu_m(a,\tau)$, and recovered humans lose immunity at rate $k_h(a,\eta)$, returning to $S_h$. Transmission occurs through bites at rate $\theta$, with per-bite transmission probabilities $\beta_m(a,\tau)$ (mosquito to human) and $\beta_h(a,\tau)$ (human to mosquito) depending on the infector's age and infection age; each population evolves by transport in $(a,\tau,\eta)$ with these rates and with new infections entering at $\tau = 0$. Let $\pi_h(a) = e^{-\int_0^a\mu_h}$, $\pi_m(a) = e^{-\int_0^a\mu_m}$, and

$$\mathcal K_{h\to m}(\xi,\tau) = \beta_h(\tau+\xi,\tau)\,e^{-\int_0^\tau(\nu_h+\gamma_h)(\sigma+\xi,\sigma)\,d\sigma}\,\frac{\pi_h(\xi+\tau)}{\int_0^\infty\pi_h}, \qquad \mathcal K_{m\to h}(\xi,\tau) = \beta_m(\tau+\xi,\tau)\,e^{-\int_0^\tau\nu_m(\sigma+\xi,\sigma)\,d\sigma}\,\frac{\pi_m(\xi+\tau)}{\int_0^\infty\pi_m},$$

the infectiousness of an infected human (resp. mosquito) of age $\xi + \tau$ and infection age $\tau$.

**Theorem.** Under standing regularity assumptions, the model generates a global, bounded, positive semiflow, and there is a disease-free equilibrium $E_0$ with $S^0_h = \Lambda_h\pi_h$, $S^0_m = \Lambda_m\pi_m$. Assuming $\beta_h, \beta_m$ are not identically zero on $\{(s+\tau,\tau)\}$, the basic reproduction number (spectral radius of the next-generation operator) satisfies

$$\mathcal R_0^2 = \frac{\Lambda_m\int_0^\infty\pi_m}{\Lambda_h\int_0^\infty\pi_h}\ \times\ \theta^2\int_0^\infty\!\!\int_0^\infty\mathcal K_{m\to h}(\xi,\tau)\,d\xi\,d\tau\ \times\ \int_0^\infty\!\!\int_0^\infty\mathcal K_{h\to m}(\xi,\tau)\,d\xi\,d\tau,$$

the product of the vector-to-host ratio, the mosquito-to-human transmission and the human-to-mosquito transmission per bite; and

1. $E_0$ is unstable if $\mathcal R_0 > 1$ and locally asymptotically stable if $\mathcal R_0 < 1$;
2. if the human rates do not depend on human age, endemic equilibria correspond to roots $K > 0$ of an explicit scalar equation $f(\mathcal R_0^2, K) = 1$, and an explicit constant $C_{\mathrm{bif}}$ (combining infection-age-weighted transmission, waning immunity and disease-induced death) decides the bifurcation at $\mathcal R_0 = 1$: backward (two endemic equilibria for $\mathcal R_0 < 1$ near $1$) if $C_{\mathrm{bif}} > 0$, forward if $C_{\mathrm{bif}} < 0$; and for $\mathcal R_0 > 1$ at least one endemic equilibrium exists.

## Depends on

- [Next-generation matrix and the basic reproduction number](../../next-generation-matrix-and-the-basic-reproductio/README.md)

## Expansion

Linearizing at $E_0$ and integrating the transport equations along characteristics expresses new infections in each species as an integral operator applied to new infections in the other; the composition human $\to$ mosquito $\to$ human is rank one in the age variables after normalization by the stationary age distributions, so its spectral radius is the product of the three scalar factors, which is $\mathcal R_0^2$ (two generations of transmission). Local stability follows from the characteristic equation of this renewal system. For endemic equilibria, solving the stationary transport equations in terms of the human force of infection $K$ reduces existence to $f(\mathcal R_0^2,K) = 1$, and the sign of $\partial_K f$ at $(1,0)$, which is proportional to $C_{\mathrm{bif}}$, determines on which side of $\mathcal R_0 = 1$ the branch of endemic equilibria emanates.

## Sources

- Quentin Richard, Marc Choisy, Thierry Lefèvre, Ramsès Djidjou-Demasse, "Human-vector malaria transmission model structured by age, time since infection and waning immunity", arXiv (2020). Section 2 (model), Theorem 3.2, Section 3.2 (formula for $\mathcal R_0$, Theorem 3.4), Section 3.3 (existence condition, $C_{\mathrm{bif}}$, Theorem 3.6). <https://doi.org/10.48550/arXiv.2012.15147>. Published version: Nonlinear Analysis: Real World Applications 63 (2022), article 103393, <https://doi.org/10.1016/j.nonrwa.2021.103393>; locators above refer to the arXiv version.
