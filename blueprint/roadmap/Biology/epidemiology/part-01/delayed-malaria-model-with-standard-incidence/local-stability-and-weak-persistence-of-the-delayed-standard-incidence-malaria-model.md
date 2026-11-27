# Local stability and weak persistence of the delayed malaria model with standard incidence

**Model.** Let $S_h, I_h$ be susceptible and infected humans and $S_v, I_v$ susceptible and infected mosquitoes, with $N_v = S_v + I_v$. Humans are infected by infected mosquitoes through standard incidence, with an incubation delay $\tau \ge 0$; mosquitoes are infected through mass action:

$$\dot S_h(t) = \beta_h - C_{vh}\frac{I_v(t)}{N_v(t)}S_h(t) - \mu_h S_h(t), \qquad \dot I_h(t) = C_{vh}\frac{I_v(t-\tau)}{N_v(t-\tau)}S_h(t-\tau) - \mu_h I_h(t),$$

$$\dot S_v(t) = \beta_v - C_{hv}I_h(t)S_v(t) - \mu_v S_v(t), \qquad \dot I_v(t) = C_{hv}I_h(t)S_v(t) - \mu_v I_v(t).$$

All parameters are positive: $\beta_h, \beta_v$ are recruitment rates, $\mu_h, \mu_v$ death rates, and $C_{vh}, C_{hv}$ infection rates. Initial data are continuous functions on $[-\tau, 0]$ with values in $[0,\infty)^4$ and $S_v + I_v > 0$.

**Well-posedness.** Solutions exist, are unique, non-negative and ultimately bounded; moreover $S_h(t-\tau) + I_h(t) \to \beta_h/\mu_h$ and $N_v(t) \to \beta_v/\mu_v$.

**Threshold.** The disease-free equilibrium is $E^0 = (\beta_h/\mu_h, 0, \beta_v/\mu_v, 0)$ and the basic reproduction number is

$$R_0 = \sqrt{\frac{C_{vh}C_{hv}\beta_h}{\mu_h^2\mu_v}}.$$

**Lemma.** There is a unique endemic equilibrium $E^*$ if and only if $R_0 > 1$.

**Theorem (local stability).** For every $\tau \ge 0$: $E^0$ is locally asymptotically stable if $R_0 < 1$ and unstable if $R_0 > 1$; and if $R_0 > 1$, then $E^*$ is locally asymptotically stable.

**Theorem (weak persistence).** If $R_0 > 1$ and $\theta \in (0,1)$, then $\limsup_{t\to\infty} I_h(t) > \theta I_h^*$ for every solution with $I_h(0) > 0$. Consequently the system is weakly persistent for all $\tau \ge 0$ when $R_0 > 1$.

In contrast with many delayed host–vector models, the incubation delay does not enter $R_0$ and cannot destabilize either equilibrium.

## Expansion

The characteristic equation at $E^0$ is

$$(\lambda + \mu_h)(\lambda + \mu_v)\big[(\lambda + \mu_h)(\lambda + \mu_v) - u_1 u_2 e^{-\lambda\tau}\big] = 0, \qquad u_1 = \frac{C_{hv}\beta_v}{\mu_v}, \quad u_2 = \frac{C_{vh}\beta_h\mu_v}{\beta_v\mu_h}.$$

Since $u_1 u_2 = R_0^2\mu_h\mu_v$, the bracketed factor has a positive real root when $R_0 > 1$, and when $R_0 < 1$ a modulus comparison on the imaginary axis shows that it has no root with non-negative real part for any $\tau$. At $E^*$ the $4 \times 4$ characteristic determinant is shown similarly to have only roots with negative real parts for every delay. Weak persistence is proved by contradiction: if $\limsup I_h \le \theta I_h^*$, then eventually $S_v > S_v^*$ and $S_h/N_v$ exceeds its endemic value, which forces $I_h$ to grow and contradicts the bound.

## Sources

- S. Guo, M. He and J.-A. Cui, "Global stability of a time-delayed malaria model with standard incidence rate", arXiv:2210.17251 (2022): model and Theorem 2.1 (Section 2); Lemma 3.1, Theorems 3.1 and 3.2 (Section 3); Theorem 4.1 and Corollary 4.1 (Section 4). <https://doi.org/10.48550/arXiv.2210.17251>. Published version: Acta Mathematicae Applicatae Sinica, English Series 39(2) (2023), 211–221, <https://doi.org/10.1007/s10255-023-1042-y>; locators above refer to the arXiv version.
