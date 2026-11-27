# Mean extinction time under demographic and environmental noise

**Statement.** In the model $dX^\varepsilon_t = b(X^\varepsilon_t)dt + \sigma(X^\varepsilon_t)dB_t + \varepsilon\sqrt{a(X^\varepsilon_t)}dW_t$ under assumption (H), with stochastic growth rate $\Lambda_0 = b'(0) - \tfrac12|\sigma'(0)|^2$ and extinction time $T^\varepsilon_0 = \inf\{t : X^\varepsilon_t = 0\}$, let the initial law $\mu$ have compact support in $(0,\infty)$. As $\varepsilon \to 0$:
1. If $\Lambda_0 < 0$, there are $C_1, C_2 > 0$ with

$$C_1|\ln\varepsilon| \lesssim \mathbb E_\mu[T^\varepsilon_0] \lesssim C_2|\ln\varepsilon|.$$

2. If $\Lambda_0 > 0$, then for each small $\gamma > 0$,

$$\varepsilon^{\,2 - (1-\gamma)\frac{4b'(0)}{|\sigma'(0)|^2}} \lesssim \mathbb E_\mu[T^\varepsilon_0] \lesssim \varepsilon^{\,2 - (1+\gamma)\frac{4b'(0)}{|\sigma'(0)|^2}},$$

so the mean extinction time grows like a power of the population size, with exponent governed by $2b'(0)/|\sigma'(0)|^2 > 1$. Moreover, when $\Lambda_0 > 0$, $T^\varepsilon_0/\mathbb E_\mu[T^\varepsilon_0]$ converges in law to a standard exponential, and the law of $X^\varepsilon_t$ is within $Ce^{-\lambda_{\varepsilon,2}t}$ in total variation of the mixture $e^{-\lambda_{\varepsilon,1}t}\langle\mu,\alpha_{\varepsilon,1}\rangle\,\mu_\varepsilon + (1 - e^{-\lambda_{\varepsilon,1}t}\langle\mu,\alpha_{\varepsilon,1}\rangle)\,\delta_0$, with $\liminf_{\varepsilon\to0}\lambda_{\varepsilon,2} > 0$.

## Expansion

Without environmental noise, demographic noise alone in a logistic model gives extinction times exponential in population size. Environmental noise proportional to density changes this to polynomial growth: near $0$ the log-density performs a Brownian motion with drift $\Lambda_0$, and the time to reach the demographic boundary layer, of width of order $\varepsilon^2$, is controlled by the scale function, producing the exponent $4b'(0)/|\sigma'(0)|^2 - 2$. When $\Lambda_0 < 0$ the population decays deterministically on the log scale and only needs time of order $|\ln\varepsilon|$ to reach the boundary layer. The multiscale statement says the process first relaxes to the quasi-stationary distribution on an $O(1)$ time scale, then leaks to extinction on the scale $1/\lambda_{\varepsilon,1}$.

## Depends on

- [Quasi-stationary concentration under small demographic noise](quasi-stationary-concentration-under-small-demographic-noise.md)

## Sources

- Alexandru Hening, Weiwei Qi, Zhongwei Shen and Yingfei Yi, "Population dynamics under demographic and environmental stochasticity", The Annals of Applied Probability 34 (2024), 5615–5663, <https://doi.org/10.1214/24-aap2101>; numbering as in arXiv:2207.08883: Theorem 2.3, Theorem 2.4 and the corollaries of Section 2.
