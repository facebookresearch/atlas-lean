# Quasi-stationary concentration under small demographic noise

**Model.** A single population with density $X^\varepsilon_t \ge 0$ follows

$$dX^\varepsilon_t = b(X^\varepsilon_t)\,dt + \sigma(X^\varepsilon_t)\,dB_t + \varepsilon\sqrt{a(X^\varepsilon_t)}\,dW_t,$$

with $B, W$ independent Brownian motions: $\sigma\,dB$ is environmental noise and $\varepsilon\sqrt{a}\,dW$ is demographic noise, $\varepsilon^2$ being inversely proportional to population size. Assume (H): $b \in C^1$, $b(0) = 0$, $b'(0) > 0$, $\limsup_{x\to\infty} b(x) < 0$; $\sigma \in C^2$, $\sigma(0) = 0$, $\sigma'(0) \ne 0$; $a \in C^2$, $a(0) = 0$, $a'(0) > 0$, $a > 0$ on $(0,\infty)$; and, as $x \to \infty$, $\limsup a/\sigma^2 < \infty$, $b/|\sigma| \to -\infty$, $xb/\sigma^2 \to -\infty$, $\limsup \frac{\sigma^2}{|b|}\max\{\frac{a'}{a}, \frac{|\sigma'|}{|\sigma|}\} = 0$ and $\limsup \frac{\sigma^2}{b^2}\max\{a'', (\sigma^2)'', |b'|\} = 0$ (satisfied e.g. by the stochastic logistic and theta-logistic models with $\sigma(x) = \sigma x$, $a(x) = \gamma x$). Then $0$ is reached in finite time a.s., and $X^\varepsilon$ has a unique quasi-stationary distribution (QSD) $\mu_\varepsilon$ on $(0,\infty)$ with density $u_\varepsilon$. Let

$$\Lambda_0 = b'(0) - \tfrac{1}{2}|\sigma'(0)|^2$$

be the stochastic growth rate at low density of the environmental-noise-only diffusion $dX^0 = b(X^0)dt + \sigma(X^0)dB$.

**Theorem.**

1. If $\Lambda_0 < 0$, then $\int_0^\infty \phi\,d\mu_\varepsilon \to 0$ as $\varepsilon \to 0$ for every bounded continuous $\phi$ with $\phi(0) = 0$: the QSD collapses onto extinction.
2. If $\Lambda_0 > 0$, then $\mu_\varepsilon \to \mu_0$ weakly and $u_\varepsilon \to u_0$ in $C^2((0,\infty))$, where $\mu_0$ is the unique stationary distribution of $X^0$ on $(0,\infty)$, with the normalized Gibbs density

    $$u_0(x) \propto \frac{1}{\sigma^2(x)}\exp\left(\int_1^x \frac{2b(y)}{\sigma^2(y)}\,dy\right).$$

The extinction rate $\lambda_{\varepsilon,1}$ (principal eigenvalue of $-\mathcal L_\varepsilon$, $\mathcal L_\varepsilon = \tfrac12(\varepsilon^2a + \sigma^2)\partial_x^2 + b\,\partial_x$) tends to $0$ in both cases.

## Expansion

When $\Lambda_0 > 0$ the environmental-noise diffusion never reaches $0$ and is positive recurrent, so as demographic noise vanishes the conditioned process should look like the persistent limit; the work is to control the singular region near $0$, where $a(x) \sim a'(0)x$ dominates $\sigma^2(x) \sim \sigma'(0)^2 x^2$ and makes the Gibbs density of $X^\varepsilon$ non-integrable. When $\Lambda_0 < 0$ the limit $X^0$ itself converges to $0$, so all quasi-stationary mass drifts to the boundary. The threshold $\Lambda_0$ is the classical invasion criterion for stochastic logistic-type models.

## Sources

- Alexandru Hening, Weiwei Qi, Zhongwei Shen and Yingfei Yi, "Population dynamics under demographic and environmental stochasticity", The Annals of Applied Probability 34 (2024), 5615–5663, <https://doi.org/10.1214/24-aap2101>; numbering as in arXiv:2207.08883: Section 2, Theorems A and B, and Proposition 3.1.
