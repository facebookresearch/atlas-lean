# Poisson CUSUM with a likelihood-ratio reference value

**Definition.** Let $y_1, y_2, \dots$ be counts monitored over time. With reference value $k$ and decision threshold $h > 0$, the one-sided cumulative-sum statistic is

$$C_0 = 0, \qquad C_i = \max\big(0,\ C_{i-1} + y_i - k\big), \quad i \ge 1,$$

and an alarm is raised at the first $i$ with $C_i > h$.

**Likelihood-ratio reference value.** To detect a shift from an in-control distribution $f(\cdot\,;\theta_0)$ to an out-of-control distribution $f(\cdot\,;\theta_1)$, the CUSUM of log-likelihood ratios $\log f(y_i;\theta_1)/f(y_i;\theta_0)$ is the sequential probability ratio test restarted at zero. For Poisson counts with in-control mean $\mu_0$ and out-of-control mean $\mu_1 > \mu_0$,

$$\log\frac{f(y;\mu_1)}{f(y;\mu_0)} = y \log\frac{\mu_1}{\mu_0} - (\mu_1 - \mu_0),$$

so the log-likelihood-ratio CUSUM is, up to the positive factor $\log(\mu_1/\mu_0)$, the count CUSUM above with

$$k = \frac{\mu_1 - \mu_0}{\log \mu_1 - \log \mu_0},$$

which satisfies $\mu_0 < k < \mu_1$ (it is the logarithmic mean of $\mu_0$ and $\mu_1$).

**Exponentially weighted alternative.** The EWMA statistic $z_0 = 0$, $z_i = \gamma y_i + (1 - \gamma) z_{i-1}$ with forgetting factor $\gamma \in (0,1]$ raises an alarm when $z_i > h$; it weights past observations geometrically instead of accumulating excesses.

## Expansion

Dividing the log-likelihood ratio by $\log(\mu_1/\mu_0) > 0$ gives $y - k$ with $k$ as stated, and the recursion $C_i = \max(0, C_{i-1} + \text{increment})$ is Page's form of repeated sequential probability ratio tests with a lower barrier at zero; by the Moustakides optimality theorem it minimizes the worst-case expected detection delay among procedures with the same in-control average run length. That $k$ lies strictly between $\mu_0$ and $\mu_1$ follows from the logarithmic-mean inequality $\sqrt{\mu_0\mu_1} < (\mu_1 - \mu_0)/\log(\mu_1/\mu_0) < (\mu_0 + \mu_1)/2$. In disease surveillance $\mu_0$ is estimated from historical counts, $\mu_1$ is the smallest increase worth detecting, and both may vary seasonally, giving a time-varying $k(t)$; $h$ is chosen to achieve a target in-control average run length (commonly set near three in-control standard deviations).

## Sources

- Siettos CI, Russo L, "Mathematical modeling of infectious disease dynamics" (2013), section "Statistical-Based Methods for Epidemic Surveillance", statistical process control methods (CUSUM with likelihood-ratio reference value and the Poisson case; EWMA), <https://doi.org/10.4161/viru.24041>, PMCID PMC3710332.
- E. S. Page, "Continuous inspection schemes", Biometrika 41 (1954) 100–115, <https://doi.org/10.2307/2333009>.
