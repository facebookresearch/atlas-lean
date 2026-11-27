# Effect of education dissemination on the HIV/AIDS endemic equilibrium

**Setting.** In the delayed HIV/AIDS model with education campaigns, general susceptibles $S_0$ meet campaign information $Z$ and move to a removed class (rate $\gamma_0$), to an abstinence or faithfulness class $S_1$ (rate $\gamma_1$), or to a condom-use class $S_2$ (rate $\gamma_2$). The information obeys $Z' = qI - \eta Z$. Put $\gamma = \gamma_0 + \gamma_1 + \gamma_2$, write $\beta_{j,u}$ for the transmission rates of the class $S_j$ under delay $u \ge 0$, and define the critical death rate $\mathcal{D}_0 = \mu(\mu + d)/B$. The ratio

$$\tau = \frac{q}{\eta}$$

measures the effective rate of education dissemination. Assume $\beta_{0,u} = \max\{\beta_{0,u}, \beta_{1,u}, \beta_{2,u}\} > \mathcal{D}_0$, and let $E^* = (S_0^*, S_1^*, S_2^*, Z^*, I^*)$ be the unique endemic equilibrium.

**Theorem (infected population).**

1. $I^*$ is non-increasing in $\tau$, and

$$\frac{B(\beta_{0,u} - \mathcal{D}_0)}{(\mu + d)(\beta_{0,u} + \tau\gamma)} \le I^* \le \min\Big\{\frac{B(\beta_{0,u} - \mathcal{D}_0)}{\mu\beta_{0,u}}, \frac{\mu}{\mathcal{D}_0}\Big\}.$$

   If $\beta_{0,u} > \min\{\beta_{1,u}, \beta_{2,u}\}$ or $\gamma_0 > 0$, then $I^*$ is strictly decreasing in $\tau$.
2. If $\mathcal{D}_0 \ge \frac{1}{\gamma}\sum_{j=1}^{2}\beta_{j,u}\gamma_j$, then $I^* \to 0$ as $\tau \to \infty$. If the inequality is strict, there is $C > 0$ with $I^* \le C/\tau$ for all $\tau > 0$, so $I^*$ decays like $\tau^{-1}$.
3. If $\mathcal{D}_0 < \frac{1}{\gamma}\sum_{j=1}^{2}\beta_{j,u}\gamma_j$, then $I^* \to I^*_\infty > 0$ as $\tau \to \infty$, where $I^*_\infty$ is the unique positive solution of $\mathcal{D}_0 = \frac{\mu}{\gamma}\sum_{j=1}^{2}\frac{\beta_{j,u}\gamma_j}{\mu + \beta_{j,u}I^*_\infty}$.

**Theorem (susceptible classes).** Under the same assumptions, as $\tau \to \infty$:

- if $\mathcal{D}_0 = \frac{1}{\gamma}\sum_j \beta_{j,u}\gamma_j$, then $(S_0^*, S_1^*, S_2^*) \to \big(0, \frac{\gamma_1 B}{\mu\gamma}, \frac{\gamma_2 B}{\mu\gamma}\big)$;
- if $\mathcal{D}_0 > \frac{1}{\gamma}\sum_j \beta_{j,u}\gamma_j$, then $(S_0^*, S_1^*, S_2^*) \to \Big(\frac{B}{\mu + \gamma Z^*_\infty}, \frac{\gamma_1 B Z^*_\infty}{\mu(\mu + \gamma Z^*_\infty)}, \frac{\gamma_2 B Z^*_\infty}{\mu(\mu + \gamma Z^*_\infty)}\Big)$, where $Z^*_\infty$ is the unique solution of $\mathcal{D}_0 = \mu\big(\beta_{0,u} + \frac{Z^*_\infty}{\mu}\sum_j \beta_{j,u}\gamma_j\big)/(\mu + \gamma Z^*_\infty)$;
- if $\mathcal{D}_0 < \frac{1}{\gamma}\sum_j \beta_{j,u}\gamma_j$, then $(S_0^*, S_1^*, S_2^*) \to \Big(0, \frac{\gamma_1 B}{\gamma(\mu + \beta_{1,u}I^*_\infty)}, \frac{\gamma_2 B}{\gamma(\mu + \beta_{2,u}I^*_\infty)}\Big)$.

**Interpretation.** Education always helps, since the endemic prevalence decreases with $\tau$. It can drive prevalence to zero only if the relative infection weight $\frac{1}{\gamma}\sum_{j=1}^{2}\beta_{j,u}\gamma_j$ of the behaviour-changed classes does not exceed the critical death rate $\mathcal{D}_0$. Otherwise residual transmission among people who adopted protective behaviour keeps a positive endemic level $I^*_\infty$, however intense the campaign.

## Depends on

- [Threshold and permanence of the delayed HIV/AIDS model with education campaigns](threshold-and-permanence-of-the-delayed-hiv-aids-model-with-education-campaigns.md)

## Expansion

The endemic level $I^*$ is the root of $G(I) = \mu + d$, where

$$G(I) = \frac{\beta_{0,u}B}{\mu + (\beta_{0,u} + \tau\gamma)I} + B\tau\sum_{j=1}^{2}\frac{\beta_{j,u}\gamma_j I}{(\mu + \beta_{j,u}I)(\mu + (\beta_{0,u} + \tau\gamma)I)}.$$

The monotonicity of $I^*$ comes from tracking how this root moves as $\tau$ grows when $\beta_{0,u}$ is the largest transmission rate. As $\tau \to \infty$ the first term vanishes and the second tends to $\frac{B}{\gamma}\sum_j \frac{\beta_{j,u}\gamma_j}{\mu + \beta_{j,u}I}$. Whether this limit can still reach $\mu + d$ for some $I > 0$ is exactly the comparison between $\frac{1}{\gamma}\sum_j \beta_{j,u}\gamma_j$ and $\mathcal{D}_0$. The susceptible limits follow by substituting the limit of $I^*$, or of $Z^* = \tau I^*$, into the equilibrium formulas.

## Sources

- D. Denu, S. Ngoma and R. B. Salako, "Analysis of a time-delayed HIV/AIDS epidemic model with education campaigns", arXiv:2101.05925 (2021): Theorem 1.3 (asymptotic behaviour of $I^*$ in $q/\eta$) and Theorem 1.4 (asymptotic behaviour of the susceptible classes), Section 1.2; proofs in Section 3. <https://doi.org/10.48550/arXiv.2101.05925>. Published version: Computational and Applied Mathematics 40(6) (2021), article 210, <https://doi.org/10.1007/s40314-021-01601-8>; locators above refer to the arXiv version.
