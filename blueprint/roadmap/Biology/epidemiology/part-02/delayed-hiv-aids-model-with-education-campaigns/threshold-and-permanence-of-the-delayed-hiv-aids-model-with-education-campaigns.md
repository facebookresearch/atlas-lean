# Threshold and permanence of the delayed HIV/AIDS model with education campaigns

**Model.** A population with recruitment rate $B$ is split into general susceptibles $S_0$ (exposed to information and education campaigns), susceptibles $S_1$ who adopted abstinence or faithfulness, susceptibles $S_2$ who adopted condom use, infected individuals $I$, and a removed class $R$ of individuals who will never be infected. The density $Z$ of campaign information grows in proportion to the number of infections and decays at rate $\eta$. With an intracellular delay $u \ge 0$ before newly infected individuals become infectious, the subsystem without $R$ reads

$$S_0'(t) = B - \gamma S_0(t)Z(t) - \beta_{0,u}S_0(t)I(t-u) - \mu S_0(t),$$

$$S_j'(t) = \gamma_j S_0(t)Z(t) - \beta_{j,u}S_j(t)I(t-u) - \mu S_j(t), \quad j = 1, 2,$$

$$Z'(t) = qI(t) - \eta Z(t), \qquad I'(t) = \sum_{j=0}^{2}\beta_{j,u}S_j(t)I(t-u) - (\mu + d)I(t),$$

where $\gamma = \gamma_0 + \gamma_1 + \gamma_2$ ($\gamma_0$ is the rate of moving to $R$), all parameters are positive, and the transmission rates $\beta_{j,u}$ do not increase with $u$. The set $\{S_0 + S_1 + S_2 + I(0) \le B/\mu,\ Z \le qB/(\mu\eta)\}$ is forward invariant.

**Threshold quantities.** The disease-free equilibrium is $E^0 = (B/\mu, 0, 0, 0, 0)$. Define

$$\mathcal{R}_{0,u} = \frac{B\beta_{0,u}}{\mu(\mu + d)}, \qquad \mathcal{D}_0 = \frac{\mu + d}{B/\mu},$$

so that $\mathcal{R}_{0,u} > 1$ if and only if $\beta_{0,u} > \mathcal{D}_0$. The critical death rate $\mathcal{D}_0$ is the per capita death rate of an infective in an entirely susceptible population.

**Theorem (disease-free equilibrium).** For every delay $u \ge 0$, $E^0$ is linearly stable if and only if $\beta_{0,u} < \mathcal{D}_0$. If moreover $\max\{\beta_{0,u}, \beta_{1,u}, \beta_{2,u}\} \le \mathcal{D}_0$, then $E^0$ is globally stable.

**Theorem (endemic equilibrium).** If $\beta_{0,u} > \mathcal{D}_0$, there is a unique endemic equilibrium $E^* = (S_0^*, S_1^*, S_2^*, Z^*, I^*)$. Here $I^*$ is the unique positive root of $G(I) = \mu + d$, where

$$G(I) = \frac{\beta_{0,u}B}{\mu + b_{0,u}I} + \frac{Bq}{\eta}\sum_{j=1}^{2}\frac{\beta_{j,u}\gamma_j I}{(\mu + \beta_{j,u}I)(\mu + b_{0,u}I)}, \qquad b_{0,u} = \beta_{0,u} + \frac{q}{\eta}\gamma,$$

and $S_0^* = B/(\mu + b_{0,u}I^*)$, $Z^* = qI^*/\eta$.

**Theorem (local stability without delay).** Let $u = 0$ and suppose $\mathcal{D}_0(\mathcal{D}_0 + \frac{q}{\eta}\gamma) \ge \frac{q}{\eta}\sum_{j=1}^{2}\beta_{j,0}\gamma_j$. There is $\beta_{0,0,\max} > \mathcal{D}_0$ such that $E^*$ is linearly stable for $\beta_{0,0} \in (\mathcal{D}_0, \beta_{0,0,\max})$; if $\beta_{0,0,\max} < \infty$, then $E^*$ is not linearly stable at $\beta_{0,0} = \beta_{0,0,\max}$.

**Theorem (permanence).** Let $u \ge 0$ and $\beta_{0,u} = \max_j \beta_{j,u} > \mathcal{D}_0$. There is $\overline{m}_u > 0$ such that every solution with admissible initial data satisfies $\liminf_{t\to\infty} I(t) > \overline{m}_u$ and

$$\frac{\mu(\beta_{0,u} - \mathcal{D}_0)}{\mathcal{D}_0(\beta_{0,u} + \frac{q}{\eta}\gamma)} \le \limsup_{t\to\infty} I(t) \le \frac{(\mu + d)(\beta_{0,u} - \mathcal{D}_0)}{\mathcal{D}_0\beta_{0,u}}.$$

Since $\beta_{0,u}$ decreases with $u$, the upper bound decreases with the delay: a longer non-infectious period (for example, viral suppression by therapy) shrinks the eventual infected population.

## Expansion

At $E^0$ only $S_0$ is present, so the linearized infected equation is the scalar delay equation $I' = \beta_{0,u}(B/\mu)I(t-u) - (\mu + d)I$; its roots all have negative real part exactly when $\beta_{0,u}B/\mu < \mu + d$, whatever the delay. Global stability under $\max_j \beta_{j,u} \le \mathcal{D}_0$ uses $S_0 + S_1 + S_2 \le B/\mu$ asymptotically, which bounds the total force of infection by $\mathcal{D}_0 \cdot B/\mu = \mu + d$. Every equilibrium is determined by its $I$-coordinate. Since $G(0) = \beta_{0,u}B/\mu > \mu + d$ when $\beta_{0,u} > \mathcal{D}_0$ and $G(I) \to 0$ as $I \to \infty$, a positive root of $G(I) = \mu + d$ exists; uniqueness needs a finer argument on the shape of $G$. Permanence is first proved in the uniform weak sense, then upgraded to uniform strong permanence by persistence theory for semiflows.

## Sources

- D. Denu, S. Ngoma and R. B. Salako, "Analysis of a time-delayed HIV/AIDS epidemic model with education campaigns", arXiv:2101.05925 (2021): model in Section 1.1; Theorem 1.1 (stability of the disease-free equilibrium), Theorem 1.2 (existence and uniqueness of the endemic equilibrium), Theorem 1.5 (linear stability of the endemic equilibrium for $u = 0$) and Theorem 1.6 (permanence), stated in Section 1.2 and proved in Sections 3–5. <https://doi.org/10.48550/arXiv.2101.05925>. Published version: Computational and Applied Mathematics 40(6) (2021), article 210, <https://doi.org/10.1007/s40314-021-01601-8>; locators above refer to the arXiv version.
