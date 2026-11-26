# Best-effort testing rate in the SIDUR model

**SIDUR model.** A population of size $N$ is split into susceptible $x_S$, undetected infected $x_I$, detected (isolated) infected $x_D$, unidentified recovered $x_U$ and identified removed $x_R$. With infection rate $\beta$, recovery rate $\gamma$, removal rate $\rho$, testing rate $u(t) \ge 0$ (tests per unit time) and testing-specificity parameter $\theta \in [0,1]$,

$$\dot x_S = -\beta x_S \frac{x_I}{N}, \quad \dot x_I = \beta x_S \frac{x_I}{N} - u\frac{x_I}{x_T} - \gamma x_I, \quad \dot x_D = u\frac{x_I}{x_T} - \rho x_D, \quad \dot x_U = \gamma x_I, \quad \dot x_R = \rho x_D,$$

where the testable population is $x_T = x_I + (1-\theta)(x_S + x_U) = \theta x_I + (1-\theta)(N - x_D - x_R)$, so a test detects an infected person with probability $x_I/x_T$.

**Effective reproduction number.** The ratio of inflow to outflow of the undetected infected compartment is

$$R_t = \frac{\beta}{u(t)/x_T(t) + \gamma}\,\frac{x_S(t)}{N},$$

and at the onset ($x_S \approx N$, $x_T \approx (1-\theta)N$) $R_0 = \beta / \big(u(0)/((1-\theta)N) + \gamma\big)$.

**Proposition (best-effort strategy for testing).** Define

$$c^*(t) = x_T(t)\,\Big|\frac{\beta(t)}{N}x_S(t) - \gamma\Big|_+ .$$

If the infection rate $\beta$ is non-increasing and $\theta$ is non-decreasing on $[t^*, t_1)$, then the minimum constant number of tests per unit time that switches the epidemic from spreading to non-spreading at $t^*$ and keeps it non-spreading on $[t^*,t_1)$ is

$$u(t) = c^*(t^*), \qquad t \in [t^*, t_1).$$

## Expansion

From the $x_I$ equation, $x_I$ is non-increasing exactly when $\beta x_S/N - \gamma - u/x_T \le 0$, i.e. $u \ge c^*(t)$ (equivalently $R_t \le 1$), which makes $c^*(t^*)$ the smallest admissible rate at $t^*$. Afterwards $c^*$ cannot increase: $x_S$ decreases, $\beta$ is non-increasing by assumption, and the testable population $x_T$ decreases on any interval where $x_I$ decreases and $\theta$ is non-decreasing (its derivative is a combination of $\dot x_I \le 0$ and the outflows of $x_S + x_U$). Hence the constant rate $c^*(t^*)$ keeps $R_t \le 1$ on the whole interval.

## Sources

- Muhammad Umar B. Niazi, Alain Kibangou, Carlos Canudas-de-Wit, Denis Nikitin, "Modeling and Control of Epidemics through Testing Policies", arXiv (2020). Section 2 (SIDUR model, testable population, reproduction numbers), Proposition 1, Lemma 6. <https://doi.org/10.48550/arXiv.2010.15438>
