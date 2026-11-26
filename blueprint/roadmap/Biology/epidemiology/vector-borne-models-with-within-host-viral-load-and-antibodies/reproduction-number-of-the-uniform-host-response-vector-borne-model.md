# Reproduction number of the uniform-host-response vector-borne model

Hosts (fractions $S, E$ of the host population, infected density $I(t,z,y)$ over viral load $z \ge z_0$ and antibody level $y \ge 0$, recovered density $R(t,y)$ over antibody level) and vectors (fractions $E_v, I_v$ exposed and infectious) interact through bites at rate $b$ with $m$ vectors per host. Within an infected host, viral load and antibodies follow the linear characteristics $\dot z = a_1 z - a_2 y$, $\dot y = a_4 z - a_3 y$; a host leaves the infected class when the viral load falls back to the detection threshold $z_0$ and its antibodies then decay as $\dot y = -a_5 y$ until they reach a protective threshold $y_0 = z_0 a_1/a_2$, after which the host is susceptible again. The full model is

$$\partial_t I + \partial_z\big((a_1 z - a_2 y)I\big) + \partial_y\big((a_4 z - a_3 y)I\big) = 0, \qquad \partial_t R - \partial_y(a_5 y R) = -I(t,z_0,y)(a_1 z_0 - a_2 y),$$

$$\dot S = -b\beta_{vh} m I_v S + a_5 y_0 R(t,y_0), \qquad \dot E = b\beta_{vh} m I_v S - E/\tau_h,$$

$$\dot E_v = b\Big(\iint I\,\beta_{hv}(z)\,dz\,dy\Big)(1 - E_v - I_v) - \Big(\frac1{\tau_v} + \mu_v\Big)E_v, \qquad \dot I_v = E_v/\tau_v - \mu_v I_v,$$

with newly infectious hosts entering at $z = z_0$ with antibody profile $g(y)$ on $[0,y_0)$; the system is well posed and conserves total host mass. Each entering host with initial antibody level $y'$ stays infected for a unique minimal time $\tau_1(y') > 0$, independent of $z_0$, and leaves with antibody level $y^+(y') > y_0$.

**Uniform host response.** If every infected host starts from the same antibody level and $\beta_{hv}$ is constant, the infected and recovered stages have fixed durations $\tau_1$ and $\tau_2 = a_5^{-1}\ln(y^+/y_0)$, and the model reduces to the distributed-delay system

$$\dot E = b\beta_{vh} m I_v\Big(1 - E - \frac1{\tau_h}\int_{t-\tau_1-\tau_2}^t E\Big) - \frac{E}{\tau_h}, \qquad \dot E_v = \frac{b\beta_{hv}}{\tau_h}\Big(\int_{t-\tau_1}^t E\Big)(1 - E_v - I_v) - \Big(\frac1{\tau_v} + \mu_v\Big)E_v,$$

$$\dot I_v = E_v/\tau_v - \mu_v I_v.$$

**Proposition.** For the uniform-host-response system let

$$\mathcal R_0 = \frac{b^2 \beta_{vh}\beta_{hv}\, m\, \tau_1}{\mu_v(\mu_v\tau_v + 1)}.$$

An endemic equilibrium $(E^*, E_v^*, I_v^*) \in (0,1)^3$ exists if and only if $\mathcal R_0 > 1$, and then

$$E^* = \frac{\mu_v\tau_h(\mathcal R_0 - 1)}{\mu_v\mathcal R_0(\tau_1 + \tau_2 + \tau_h) + b\beta_{hv}\tau_1}, \qquad E_v^* = \frac{\mu_v\tau_v(\mathcal R_0 - 1)}{\mathcal R_0(1 + \mu_v\tau_v) + b\beta_{vh} m(\tau_1 + \tau_2 + \tau_h)}.$$

For the full model the same threshold holds with $\tau_1$ replaced by the **mean infective permanence** (the average of $\tau_1(y)$ weighted by the entry flux $g(y)(a_1 z_0 - a_2 y)$) and $\beta_{hv}\tau_1$ by the corresponding average of $\int_0^{\tau_1(y)}\beta_{hv}(z(\tau,y))\,d\tau$.

## Expansion

$\mathcal R_0$ is the product of the two transmission legs: one infectious host, during its infectious period $\tau_1$, infects $b\beta_{hv}\tau_1$ susceptible vectors per vector-per-host ratio; a newly infected vector survives the extrinsic incubation with probability $1/(1 + \mu_v\tau_v)$ and then bites for a mean time $1/\mu_v$, infecting $b\beta_{vh} m$ hosts per unit time. The within-host model enters only through $\tau_1$ (and $\tau_2$ in the endemic level), so faster antibody responses shorten $\tau_1$ and lower $\mathcal R_0$, while longer antibody protection ($\tau_2$) lowers the endemic prevalence without changing the threshold. Setting derivatives to zero with constant histories reduces equilibria to one scalar equation whose positive root exists exactly when $\mathcal R_0 > 1$.

## Sources

- Paulo Amorim, Maria Soledad Aronna, Debora de Oliveira Medeiros, "A structured model of vector-borne disease with within-host viral load and antibody dynamics", arXiv (2026). Section 2 (full model), Section 3 (Propositions 3.1, 3.3 and 3.5, Theorem 3.4), Section 4 (reduction to the delay system, equation for $\tau_2$, Proposition 4.1). <https://doi.org/10.48550/arXiv.2605.25370>
