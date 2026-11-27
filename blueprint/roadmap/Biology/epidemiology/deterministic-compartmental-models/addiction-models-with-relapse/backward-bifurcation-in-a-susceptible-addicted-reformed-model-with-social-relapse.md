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

there is no endemic equilibrium for $R_0 < R_c$ and, when relapse is strong in the sense $R_\phi(1 - R_\mu) > 1$ (equivalently $\phi\gamma > (\mu + \gamma)^2$), two endemic equilibria for $R_c < R_0 < 1$: a backward bifurcation, in which addiction can persist below $R_0 = 1$. If $R_\phi(1 - R_\mu) \le 1$ there is no endemic equilibrium for $R_0 < 1$. (Section 3.2.1 of arXiv:2210.15481 states the two equilibria on $(R_c, 1)$ without this condition; it is needed: for $R_\phi = 1.5$, $R_\mu = 0.5$, $R_0 = 0.99$ one has $R_c \approx 0.977 < R_0 < 1$, but all three coefficients of the quadratic are positive.)
3. *With willingness factor* ($0 < \nu \le 1$). Endemic equilibria are $s^* = \mu D/(\beta\kappa a + \mu D)$ with $D = 1 + \nu\gamma a/(\phi a + \mu)$, $\tilde s^* = \gamma a/(\phi a + \mu)$, with $a > 0$ a root of the cubic

$$f(a) = R_\phi^2R_0\,a^3 + R_\phi\big[R_0(1 - R_\phi) + R_\mu(R_0 + R_\phi) + \nu R_\mu(1 - R_\mu)\big]a^2 + R_\mu\big[\nu(1 - R_\mu) + R_0(1 - R_\phi) + R_\phi(1 - R_0) + R_\mu R_\phi\big]a + R_\mu^2(1 - R_0).$$

   Varying $R_0$ through $\kappa$ with the other parameters fixed, let $R_c(\nu) < R_0^*(\nu)$ be the two values of $R_0$ at which $f$ has a double root. These thresholds depend on $\nu$ and differ from the $\nu = 0$ value $R_c$ above: for $\mu = 0.00015$, $\gamma = 0.0027$, $\beta = 0.009$, $\nu = 0.8$ and $\phi = 0.0044$, two endemic equilibria appear from $R_0 \approx 0.90$ (and three exist up to $R_0^*(\nu) \approx 1.03$), while the $\nu = 0$ formula gives $0.6495$. Then two positive equilibria require $0 < R_c(\nu) < R_0 < 1$ and $R_\phi > 1$; three positive equilibria require $1 < R_0 < R_0^*(\nu)$ and $R_\phi > 1$; and $1 < R_0^*(\nu) < R_0$ with $R_\phi > 1$ suffices for a unique positive equilibrium. So a forward–backward bifurcation, with multiple endemic states above $R_0 = 1$, can occur.

## Proof sketch

At an endemic state the addicted equation reduces to $R_0 s^* g(\tilde s^*)/\kappa + R_\phi\tilde s^* = 1$; inserting the equilibrium expressions for $s^*$ and $\tilde s^*$ gives the polynomial in $a$. By Descartes' rule, for $\nu = 0$ the constant term changes sign at $R_0 = 1$ while the linear coefficient is negative only for $R_0 > R_\mu R_\phi/(R_\phi - 1)$ (with $R_\phi > 1$). For $R_0 < 1$ two positive roots need both this and a positive discriminant; $R_c$ is where the discriminant vanishes, and both hold on $(R_c, 1)$ exactly when $R_\phi(1 - R_\mu) > 1$. Relapse acts as a positive feedback: each reformed individual is a susceptible with higher per-contact "infection" rate, the classic mechanism behind backward bifurcations in drinking and opioid-use models.

## Sources

- Fabio Sanchez, Jorge Arroyo-Esquivel and Juan G. Calvo, "A mathematical model with nonlinear relapse: conditions for a forward-backward bifurcation", *Journal of Biological Dynamics* 17 (2023), 2192238, <https://doi.org/10.1080/17513758.2023.2192238>. Preprint version: arXiv:2210.15481 (2022), Section 3 (basic reproductive number, endemic equilibria for $\nu = 0$ and $0 < \nu \le 1$, and the propositions on numbers of equilibria), <https://doi.org/10.48550/arXiv.2210.15481>.
