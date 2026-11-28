# Power-law mean fitness under diminishing-returns epistasis

**Model (daily batch culture).** Each day $i$ starts with $N$ founder cells; founder $j$ carries relative Malthusian fitness $r_{ij}$ (with $r_{0j} \equiv 1$) and founds an independent Yule clone that branches at rate $r_{ij}$ until the growth time $\sigma_i$ defined by $\sum_{j=1}^N e^{r_{ij}\sigma_i} = \gamma N$, where $\gamma > 1$ is the daily dilution factor. The next day's $N$ founders are sampled from the $\gamma N$ cells. With probability $\mu$ one new founder carries a beneficial mutation, which raises the fitness $r$ of its background to $r + \delta(r)$ with

$$\delta(r) = \frac{\varphi}{r^{q}}, \qquad \varphi > 0, \; q \ge 0,$$

so $q > 0$ is diminishing-returns epistasis. The mean relative fitness on day $i$ is the effective reproduction rate

$$F_i = \frac{1}{\sigma_i} \log\Big(\frac{1}{N}\sum_{j=1}^N e^{r_{ij}\sigma_i}\Big).$$

In a homogeneous population of fitness $F$ the growth period is $\sigma(F) = \log\gamma / F$, a mutant has selective advantage $s(F) = \delta(F)\sigma(F)$, and its fixation probability is $\pi(F) \sim C\, s(F)$ with $C = \gamma/(\gamma - 1)$. Set $\Gamma_N = C \mu_N \varphi_N^2 \log\gamma$.

**Theorem (law of large numbers).** Let $\mu_N \sim N^{-a}$ and $\varphi_N \sim N^{-b}$ with

$$0 < b < \tfrac12, \qquad a > 3b$$

(weak mutation, moderate selection, no clonal interference). Then, as $N \to \infty$, the rescaled fitness process $\big(F^N_{\lfloor \tau/\Gamma_N \rfloor}\big)_{\tau \ge 0}$ converges in distribution, locally uniformly in $\tau$, to the deterministic function

$$f(\tau) = \big(1 + 2(1+q)\,\tau\big)^{\frac{1}{2(1+q)}},$$

the solution of $f'(\tau) = f(\tau)^{-(2q+1)}$, $f(0) = 1$. The mean fitness curve is therefore a concave power law.

## Proof depends on

- [Fixation probability of a beneficial mutation under serial transfer](../fixation-probability-of-a-beneficial-mutation-under-serial-transfer.md)

## Expansion

The expected daily fitness gain in a population at fitness $F$ is $\mathbb{E}(\Delta F \mid F) \approx \mu\, \pi(F)\, \delta(F) \sim \Gamma/F^{2q+1}$: the increment $\varphi/F^q$ appears twice (in the gain and in the fixation probability), and one extra factor $1/F$ comes from the shorter growth period of fitter populations (the runtime effect). Since $a > 3b$, mutations are rare enough that each one fixes or is lost before the next arrives, so with high probability at most two fitness classes coexist, and the law of large numbers replaces the expectation in the recursion by the ODE. Even with $q = 0$ (additive fitness) the runtime effect makes the curve concave, $f(\tau) = \sqrt{1 + 2\tau}$. The model was built to explain the decelerating fitness trajectory observed in Lenski's *E. coli* long-term evolution experiment.

## Sources

- E. Baake and A. Wakolbinger, "Microbial populations under selection", in *Probabilistic Structures in Evolution* (E. Baake and A. Wakolbinger, eds.), EMS Series of Congress Reports, EMS Press (2021), 43–68, <https://doi.org/10.4171/ECR/17-1/3>; preprint arXiv:2004.01011 (2020), Section 2 ("Modelling Lenski's long-term evolution experiment"): intraday and interday dynamics, the heuristic for the power law, and Theorem 2.1 (law of large numbers), <https://doi.org/10.48550/arXiv.2004.01011>.
- Adrián González Casanova, Noemi Kurt, Anton Wakolbinger and Linglong Yuan, "An individual-based model for the Lenski experiment, and the deceleration of the relative fitness", *Stochastic Processes and their Applications* 126 (2016), 2211–2252, <https://doi.org/10.1016/j.spa.2016.01.009> (original proof of the law of large numbers).
