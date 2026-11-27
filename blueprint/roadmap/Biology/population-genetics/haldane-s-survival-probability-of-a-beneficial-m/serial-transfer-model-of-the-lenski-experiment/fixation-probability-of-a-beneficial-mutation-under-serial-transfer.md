# Fixation probability of a beneficial mutation under serial transfer

**Serial-transfer model.** Each day starts with $N$ bacteria. Within a day, cells split by binary fission (independent Yule processes): wild-type cells at rate $r$, mutant cells at rate $r + \varrho_N$. Growth is stopped at the deterministic time $\sigma_k = \inf\{t \ge 0 : \mathbb E[Y_t] \ge \gamma N\}$, where $\gamma > 1$ is the daily expansion factor, $k$ is the number of mutants at the start of the day and $Y_t$ is the total population. The next day's founders are a uniform sample of $N$ cells without replacement from the end-of-day population. So, given $k$ mutants at the start of day $i-1$, the end-of-day mutant and wild-type counts are independent negative binomials with parameters $(k, e^{-(r+\varrho_N)\sigma_k})$ and $(N-k, e^{-r\sigma_k})$. The number $K_i$ of mutants among the new founders is hypergeometric given these counts.

Assume moderately strong selection:

$$\varrho_N \sim N^{-b} \quad \text{for some } b \in (0, \tfrac12).$$

**Theorem.** Let a single mutant be present at day $0$ ($K_0 = 1$), with no further mutation.

1. (Selective advantage per day.) $\mathbb E[K_1 \mid K_0 = 1] - 1 \sim \varrho_N \dfrac{\log\gamma}{r}$ as $N \to \infty$.
2. (Fixation probability.) With $C(\gamma) := \dfrac{\gamma\log\gamma}{\gamma - 1}$,

$$\pi_N := \mathbb P(\exists\, i : K_i = N \mid K_0 = 1) \;\sim\; \varrho_N\,\frac{C(\gamma)}{r}, \qquad N \to \infty .$$

3. (Duration of the sweep.) With $\tau^N$ the first day on which the mutant is fixed or lost, for every $\delta > 0$ and all large $N$,

$$\mathbb P\bigl(\tau^N > \varrho_N^{-1-3\delta}\bigr) \le (7/8)^{\varrho_N^{-\delta}} .$$

The fixation probability is therefore larger than the per-day selective advantage $s_N = \varrho_N\log\gamma/r$ by the factor $\gamma/(\gamma-1)$. This factor is the reciprocal of the variance factor of the daily offspring law, so it is the analogue of Haldane's $2s/\sigma^2$ for this Cannings model.

## Expansion

In the early phase of the sweep the mutant count is sandwiched between two near-critical Galton–Watson processes. Each mutant founder leaves a geometric number of end-of-day descendants, and each is retained by the sampling with probability about $1/\gamma$. That gives a mixed-binomial offspring law with mean $1 + s_N + o(\varrho_N)$ and variance about $2(1 - 1/\gamma)$. A branching process with mean $1 + s$ and offspring variance $v$ survives with probability $\sim 2s/v$, which gives $2\varrho_N(\log\gamma/r)/(2(1-1/\gamma)) = \varrho_N C(\gamma)/r$. Once the mutant reaches size $\varepsilon N$ it fixes with high probability, and both phases take $O(\varrho_N^{-1-\delta})$ days. On the time scale $(\varrho_N\mu_N)^{-1}$, with $\mu_N$ the per-day mutation probability, successful mutations then arrive as a Poisson process of rate $C(\gamma)/r_0$, where $r_0$ is the day-$0$ reproduction rate.

## Sources

- Adrián González Casanova, Noemi Kurt, Anton Wakolbinger, Linglong Yuan, "An individual-based model for the Lenski experiment, and the deceleration of the relative fitness", *Stochastic Processes and their Applications* 126 (2016), 2211–2252, <https://doi.org/10.1016/j.spa.2016.01.009>; preprint arXiv:1505.01751, <https://doi.org/10.48550/arXiv.1505.01751>. Numbering of the arXiv version: Section 2: Proposition 2.6 (model with selection), Proposition 2.8, Theorem 2.9, Theorem 2.13; proofs in Section 3.
