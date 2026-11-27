# Poisson-binomial convolution model for secondary events and its weak dependence

**Model.** Let $X_t$ be the number of primary events (e.g. cases) on day $t$ and $Y_t$ the number of secondary events (e.g. deaths) on day $t$. A primary event on day $s$ leads to a secondary event with probability $p_s$ (the time-varying severity rate), and given that it does, the delay is $k$ days with probability $\pi^{(s)}_k$, $\sum_{k\ge0}\pi^{(s)}_k = 1$. Writing

$$Y_t = \sum_{k\ge0}\sum_{i=1}^{X_{t-k}} \mathbf 1\{\text{primary event } i \text{ of day } t-k \text{ leads to a secondary event on day } t\}, \qquad \mathbf 1\{\cdots\} \sim \operatorname{Bernoulli}\big(p_{t-k}\pi^{(t-k)}_k\big),$$

with independent indicators across individuals,

$$Y_t \mid X_{s\le t} \sim \operatorname{PoissonBinomial}\big(\underbrace{\pi^{(t)}_0p_t,\dots}_{X_t},\ \underbrace{\pi^{(t-1)}_1p_{t-1},\dots}_{X_{t-1}},\ \dots\big),$$

with mean $\mu_t = \sum_{k\ge0} X_{t-k}\,\pi^{(t-k)}_k p_{t-k}$, a convolution of primary counts with the delay distribution weighted by the severity rate.

**Poisson approximation.** By the Barbour–Hall bound, the total variation distance between this Poisson-binomial law and the Poisson law with mean $\mu_t$ is at most $\sum_{k\ge0}\big(\pi^{(t-k)}_kp_{t-k}\big)^2$, which is negligible for small severity rates; this justifies the likelihood $Y_t \mid X \sim \operatorname{Poisson}(\mu_t)$ used for deconvolution.

**Proposition (weak dependence of successive days).** Assume $\operatorname{Var}(Y_t \mid X_{s\le t}) = \operatorname{Var}(Y_{t+1} \mid X_{s\le t+1})$. Then

$$\operatorname{Cor}(Y_t, Y_{t+1} \mid X_{s\le t+1}) \in \bigg[\frac{-\max_{k\ge0}\pi^{(t-k)}_kp_{t-k}}{1 - \max_{k\ge0}\pi^{(t-k)}_kp_{t-k}},\ 0\bigg].$$

Successive secondary counts are negatively correlated (an individual who dies on day $t$ cannot die on day $t+1$), but the correlation is of the order of the largest per-day success probability, so treating them as conditionally independent is a mild approximation.

## Expansion

For an individual from day $s$, the indicators of a secondary event on days $t$ and $t+1$ are mutually exclusive, so their covariance is $-q_tq_{t+1}$ with $q_t = p_s\pi^{(s)}_{t-s}$; individuals are independent, so $\operatorname{Cov}(Y_t,Y_{t+1}) = -\sum X_s q_t q_{t+1} \le 0$. Each term satisfies $q_tq_{t+1} \le \frac{\max q}{1-\max q}\,q_{t+1}(1-q_{t+1})$, and summing against the Poisson-binomial variance $\sum X_s q_{t+1}(1-q_{t+1})$ under the equal-variance assumption gives the lower bound on the correlation.

## Sources

- Jeremy Goldwasser, Addison J. Hu, Alyssa Bilinski, Daniel J. McDonald, Ryan J. Tibshirani, "Estimating time-varying epidemic severity rates with adaptive deconvolution", The Annals of Applied Statistics 20 (2026), 2518–2544, <https://doi.org/10.1214/26-aoas2216>. Published version of arXiv:2510.16180, cited next; locators there refer to the arXiv version.
- Jeremy Goldwasser, Addison J. Hu, Alyssa Bilinski, Daniel J. McDonald, "Estimating Time-Varying Epidemic Severity Rates with Adaptive Deconvolution", arXiv (2025). Section 2 (exact and approximate likelihood), Proposition 2.1. <https://doi.org/10.48550/arXiv.2510.16180>
