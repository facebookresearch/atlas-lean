# Reproduction number estimation with imported cases and serial-interval uncertainty

**Setting.** Time is discrete, $t = 0, 1, 2, \dots$. At each step the incidence splits into locally infected and imported cases,

$$I_t = I_t^{\mathrm{local}} + I_t^{\mathrm{imported}},$$

both observed. Let $w = (w_s)_{s \ge 1}$ be a discretized serial-interval distribution ($w_s \ge 0$, $\sum_s w_s = 1$, $w_0 = 0$). The total infectiousness at time $t$ is

$$\Lambda_t(w) = \sum_{s=1}^{t} I_{t-s}\, w_s = \sum_{s=1}^{t}\big(I_{t-s}^{\mathrm{local}} + I_{t-s}^{\mathrm{imported}}\big) w_s ,$$

so imported cases contribute to infectiousness but are never counted as offspring.

**Model.** Over a window $W_t = \{t-\tau, \dots, t\}$ the reproduction number $R_t$ is constant and, conditionally on past incidence and $w$,

$$I_k^{\mathrm{local}} \sim \mathrm{Poisson}\big(R_t\, \Lambda_k(w)\big), \qquad k \in W_t,$$

independently. The prior is $R_t \sim \mathrm{Gamma}(\text{shape } a, \text{scale } b)$.

**Proposition (conjugate posterior).** Conditionally on $w$, the posterior of $R_t$ is a gamma law with

$$\text{shape } a + \sum_{k \in W_t} I_k^{\mathrm{local}}, \qquad \text{scale } \Big(\sum_{k \in W_t} \Lambda_k(w) + \frac{1}{b}\Big)^{-1},$$

so its mean is $\big(a + \sum_{k} I_k^{\mathrm{local}}\big)\big/\big(\sum_k \Lambda_k(w) + 1/b\big)$.

**Integration over the serial interval.** If $w^{(1)}, \dots, w^{(n)}$ is a posterior sample of serial-interval distributions (obtained from interval-censored onset times of index–secondary pairs), the posterior of $R_t$ given both data sources is the equal-weight mixture

$$p(R_t \mid \text{incidence}, \text{pairs}) \approx \frac{1}{n} \sum_{i=1}^{n} \mathrm{Gamma}\Big(a + \sum_{k \in W_t} I_k^{\mathrm{local}},\ \big(\textstyle\sum_{k \in W_t} \Lambda_k(w^{(i)}) + 1/b\big)^{-1}\Big),$$

sampled by drawing $m$ values of $R_t$ from each component.

**Discretization.** A continuous serial-interval density $g$ is converted to $w_s = \int_{s-1/2}^{s+1/2} g(x)\,dx$ for $s \ge 1$, $w_0 = 0$, then renormalized to sum to $1$.

## Expansion

The likelihood over the window is $\prod_{k \in W_t} (R_t\Lambda_k)^{I_k^{\mathrm{local}}} e^{-R_t\Lambda_k} / I_k^{\mathrm{local}}!$. As a function of $R_t$ it is proportional to $R_t^{\sum_k I_k^{\mathrm{local}}} e^{-R_t \sum_k \Lambda_k}$; multiplying by the gamma density $R_t^{a-1}e^{-R_t/b}$ gives a gamma kernel with the stated shape and rate $\sum_k \Lambda_k + 1/b$. Treating imported cases as infectors but not infectees removes the upward bias that arises when every case is attributed to local transmission, which matters most early in an outbreak when importations dominate. The mixture over $w^{(i)}$ propagates serial-interval uncertainty, which widens the credible interval of $R_t$ when only a few transmission pairs are available. The source chooses $a, b$ so the prior has mean and standard deviation $5$.

## Sources

- R. N. Thompson, J. E. Stockwin, R. D. van Gaalen, J. A. Polonsky, Z. N. Kamvar, P. A. Demarsh, E. Dahlqwist, S. Li, E. Miguel, T. Jombart, J. Lessler, S. Cauchemez, A. Cori, "Improved inference of time-varying reproduction numbers during infectious disease outbreaks", Epidemics 29 (2019) 100356, Sections 2.1–2.2, <https://doi.org/10.1016/j.epidem.2019.100356> (PMC7105007).
