# Backward bifurcation in a susceptible–addicted–reformed model with social-influence relapse

**Model.** Population fractions of at-risk susceptibles $s$, addicted $a$ and reformed $\tilde s$ ($s + a + \tilde s = 1$) satisfy

$$\dot s = \mu - \beta g(\tilde s)sa - \mu s, \qquad \dot a = \beta g(\tilde s)sa + \phi\tilde s a - (\mu + \gamma)a, \qquad \dot{\tilde s} = \gamma a - \phi\tilde s a - \mu\tilde s,$$

where $\mu$ is the turnover rate, $\gamma$ the recovery (reform) rate, $\phi$ the relapse rate of reformed individuals through contact with addicted ones, and $g(\tilde s) = \kappa/(1 + \nu\tilde s)$, $\nu \in [0,1]$, is a decreasing "willingness" factor by which reformed individuals discourage initiation.

**Thresholds.**

$$R_0 = \frac{\beta\kappa}{\mu + \gamma}, \qquad R_\phi = \frac{\phi}{\mu + \gamma}, \qquad R_\mu = \frac{\mu}{\mu + \gamma} \in (0,1).$$

**Theorem.**
1. The addiction-free equilibrium $(1, 0, 0)$ is locally asymptotically stable iff $R_0 < 1$ (Jacobian eigenvalues $-\mu, -\mu, \beta\kappa - (\mu + \gamma)$).
2. *No willingness factor* ($\nu = 0$). Endemic equilibria are $s^* = \mu/(\beta\kappa a + \mu)$, $\tilde s^* = \gamma a/(\phi a + \mu)$ with $a > 0$ a root of

$$R_\phi R_0\,a^2 + \big(R_0(1 - R_\phi) + R_\mu R_\phi\big)a + R_\mu(1 - R_0) = 0.$$

For $R_0 > 1$ there is exactly one positive root. With

$$R_c = R_\mu R_\phi\,\frac{1 + R_\phi + 2\sqrt{R_\phi(1 - R_\mu)}}{(R_\phi - 1)^2 + 4R_\mu R_\phi},$$

there is no endemic equilibrium for $R_0 < R_c$ and, when relapse is strong ($R_\phi > 1$), two endemic equilibria for $R_c < R_0 < 1$: a backward bifurcation, in which addiction can persist below $R_0 = 1$.
3. *With willingness factor* ($\nu > 0$). Endemic $a$ solves a cubic; two positive equilibria require $0 < R_c < R_0 < 1$ and $R_\phi > 1$; three positive equilibria require $1 < R_0 < R_0^*$ and $R_\phi > 1$; and $1 < R_0^* < R_0$ with $R_\phi > 1$ suffices for a unique positive equilibrium, for an explicit threshold $R_0^*$. So a forward–backward bifurcation, with multiple endemic states above $R_0 = 1$, can occur.

## Proof sketch

At an endemic state the addicted equation reduces to $R_0 s^* g(\tilde s^*)/\kappa + R_\phi\tilde s^* = 1$; inserting the equilibrium expressions for $s^*$ and $\tilde s^*$ gives the polynomial in $a$. By Descartes' rule, for $\nu = 0$ the constant term changes sign at $R_0 = 1$ while the linear coefficient can be negative only if $R_\phi > 1$, so two positive roots below threshold require strong relapse, and $R_c$ is where the discriminant vanishes. Relapse acts as a positive feedback: each reformed individual is a susceptible with higher per-contact "infection" rate, the classic mechanism behind backward bifurcations in drinking and opioid-use models.

## Sources

- Fabio Sanchez, Jorge Arroyo-Esquivel and Juan G. Calvo, "A mathematical model with nonlinear relapse: conditions for a forward-backward bifurcation", *Journal of Biological Dynamics* 17 (2023), 2192238, <https://doi.org/10.1080/17513758.2023.2192238>. Preprint version: arXiv:2210.15481 (2022), Section 3 (basic reproductive number, endemic equilibria for $\nu = 0$ and $0 < \nu \le 1$, and the propositions on numbers of equilibria), <https://doi.org/10.48550/arXiv.2210.15481>.
