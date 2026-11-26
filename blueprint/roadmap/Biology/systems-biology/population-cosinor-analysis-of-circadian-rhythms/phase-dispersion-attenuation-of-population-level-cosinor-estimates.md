# Phase-dispersion attenuation of population-level cosinor estimates

**Setting.** Individual $i$ in a cohort is sampled at clock times $X_{ij}$ (hours) and follows an amplitude–phase trigonometric (cosinor) model of order $K$ with a 24-hour period,

$$Y_{ij} = \theta_{i,0} + \sum_{k=1}^K \theta_{i,2k-1}\cos\Big(\frac{k\pi X_{ij}}{12} + \theta_{i,2k}\Big) + \epsilon_{ij},$$

with amplitudes $\theta_{i,2k-1}$ and phase shifts $\theta_{i,2k}$. Individual parameters are random around population values, $\theta_i = \beta + b_i$ with $\mathbb{E}\,b_i = 0$. Equivalently $Y_{ij} = \gamma_{i,0} + \sum_k \big(\gamma_{i,2k-1}\sin(k\pi X_{ij}/12) + \gamma_{i,2k}\cos(k\pi X_{ij}/12)\big) + \epsilon_{ij}$ with $\gamma_{i,2k-1} = -\theta_{i,2k-1}\sin\theta_{i,2k}$ and $\gamma_{i,2k} = \theta_{i,2k-1}\cos\theta_{i,2k}$. The **standard two-stage (STS)** method fits each individual by least squares in the linear parametrisation and averages the coefficient vectors $\hat\gamma_i$ across individuals.

**Proposition.** Suppose each individual has $n > 2K$ equally spaced samples over 24 hours, $X_{ij} = 24(j-1)/n$, and the phase deviations $b_{i,2k}$ are independent of the other random effects. Then the STS population coefficients satisfy $\mathbb{E}\hat\alpha_0 = \alpha_0$ and

$$\mathbb{E}\hat\alpha_{2k-1} = \alpha_{2k-1}\,\mathbb{E}\cos b_{i,2k} - \alpha_{2k}\,\mathbb{E}\sin b_{i,2k}, \qquad \mathbb{E}\hat\alpha_{2k} = \alpha_{2k}\,\mathbb{E}\cos b_{i,2k} + \alpha_{2k-1}\,\mathbb{E}\sin b_{i,2k},$$

where $\alpha_{2k-1} = -\beta_{2k-1}\sin\beta_{2k}$ and $\alpha_{2k} = \beta_{2k-1}\cos\beta_{2k}$ are the true population coefficients.

**Corollary (attenuation).** The population amplitude recovered from the STS estimates is

$$\sqrt{(\mathbb{E}\hat\alpha_{2k-1})^2 + (\mathbb{E}\hat\alpha_{2k})^2} = \beta_{2k-1}\,\big|\varphi_{b_{i,2k}}(1)\big|,$$

where $\varphi_{b}$ is the characteristic function of the individual phase deviation, and the recovered phase is rotated by the mean direction of $b_{i,2k}$. Because $|\varphi(1)| \le 1$, with equality only for degenerate phase deviations, the STS amplitude is biased towards zero whenever individuals peak at different times, and Wald tests of zero amplitude lose power accordingly.

## Expansion

With equally spaced samples over a full cycle the design matrix of sines and cosines is orthogonal, $W^\top W = \mathrm{diag}(n, n/2, \dots, n/2)$, so each individual's least-squares coefficients are unbiased for $\gamma_i$, and averaging gives $\mathbb{E}\gamma_i$. Writing $\gamma_{i,2k-1} + i\gamma_{i,2k}$ as a complex number, it equals $i\theta_{i,2k-1} e^{i\theta_{i,2k}}$, whose expectation factorises as $i\beta_{2k-1}e^{i\beta_{2k}}\,\mathbb{E}e^{i b_{i,2k}}$ when amplitude and phase deviations are independent; taking the modulus gives the factor $|\varphi(1)|$. Averaging sinusoids with different phases partly cancels them, the same mechanism by which desynchronised cellular clocks produce damped tissue-level rhythms. The refined two-stage method converts each $\hat\gamma_i$ into an amplitude and the sine and cosine of the phase before averaging, which removes the attenuation and avoids averaging angles across the $\pm\pi$ boundary; inference then uses the delta method or a bootstrap that resamples individuals and residuals.

## Sources

- Michael T. Gorczyca, Jenna D. Li, Charissa M. Newkirk, Arjun S. Srivatsa, Hugo F. M. Milan, "Two-Stage Trigonometric Regression for Modeling Circadian Rhythms", arXiv:2510.08309 (2025), Section 2 (models, standard two-stage method, Proposition 1, Corollary 1, refined two-stage method, bootstrap) and Appendix (Lemmas 1–3), <https://doi.org/10.48550/arXiv.2510.08309>.
