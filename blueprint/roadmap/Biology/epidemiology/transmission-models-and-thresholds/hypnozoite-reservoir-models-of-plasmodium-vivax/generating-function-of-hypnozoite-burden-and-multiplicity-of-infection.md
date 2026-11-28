# Generating function of hypnozoite burden and multiplicity of infection

**Within-host model.** Infective bites arrive at a host as a Poisson process with time-dependent rate $a I_M(t)$ (the force of reinfection, $I_M$ being the proportion of infected mosquitoes). Each bite starts one primary blood-stage infection, cleared at rate $\gamma$, and deposits a batch of hypnozoites with geometric law $P(k) = \frac{1}{\nu+1}\big(\frac{\nu}{\nu+1}\big)^k$, $k \ge 0$ (mean $\nu$). Each hypnozoite independently stays dormant (state $H$), activates at rate $\alpha$ into a relapse (state $A$) that is cleared at rate $\gamma$ (state $C$), or dies at rate $\mu$ (state $D$). For $\alpha + \mu \ne \gamma$, the state probabilities $t$ time units after inoculation are

$$p_H(t) = e^{-(\alpha+\mu)t}, \qquad p_A(t) = \frac{\alpha}{(\alpha+\mu)-\gamma}\big(e^{-\gamma t} - e^{-(\alpha+\mu)t}\big).$$

**Theorem.** Let $H_{i,j}(t)$ be the probability that at time $t$ a host has $i$ hypnozoites in the liver and multiplicity of blood-stage infection $j$ (ongoing primary infections plus relapses), starting from an uninfected host, $H_{0,0}(0) = 1$. Then for $(x,y) \in [0,1]^2$

$$\sum_{i,j\ge0} H_{i,j}(t)\,x^iy^j = \exp\left\{-a\int_0^t I_M(\tau)\left(1 - \frac{1 + (y-1)e^{-\gamma(t-\tau)}}{1 + \nu(1-x)\,p_H(t-\tau) + \nu(1-y)\,p_A(t-\tau)}\right)d\tau\right\}.$$

In particular the probability of current blood-stage infection is

$$I_H(t) = 1 - \exp\left\{-a\int_0^t I_M(\tau)\,z(t-\tau)\,d\tau\right\}, \qquad z(s) = \frac{e^{-\gamma s} + \nu p_A(s)}{1 + \nu p_A(s)} = 1 - (1 - e^{-\gamma s})\frac{1}{1 + \nu p_A(s)},$$

where $z(s)$ is the probability that a single bite still causes blood-stage infection $s$ time units later. The same $H_{i,j}$ solve the countable system of forward equations for the population proportions in each hypnozoite/MOB state; with $\nu = 0$ (no hypnozoites) it reduces to the classical superinfection model for *P. falciparum*.

## Expansion

Treat each bite's primary infection and each hypnozoite as a customer in an open network of infinite-server queues with nodes $H, A, C, D$ and primary-infection nodes; customers move independently, and arrivals come in batches at the times of a non-homogeneous Poisson process. A bite at time $\tau$ contributes, at time $t$, a primary infection still present with probability $e^{-\gamma(t-\tau)}$ and an independent geometric batch whose members are each in $H$ or $A$ with probabilities $p_H(t-\tau)$, $p_A(t-\tau)$. The probability generating function of one bite's contribution is therefore $\frac{1 + (y-1)e^{-\gamma(t-\tau)}}{1 + \nu(1-x)p_H + \nu(1-y)p_A}$ (geometric thinning), and the Poisson marking theorem turns the superposition over bites into the exponential formula. Setting $x = 1$, $y = 0$ gives $1 - I_H$.

## Sources

- S. Mehra, J. M. McCaw, P. G. Taylor, "Superinfection and the hypnozoite reservoir for Plasmodium vivax: a general framework", Journal of Mathematical Biology 88 (2024) 7, Eqs. (2)–(6), (20)–(24), <https://doi.org/10.1007/s00285-023-02014-3>, PMCID PMC10692056.
