# Piecewise ABC factorisation of the posterior of a discretely observed Markov model

**Setting.** Let $\theta \in \mathbb{R}^d$ have prior density $\pi(\theta)$ and let $x = (x_1,\dots,x_n)$, $x_i = x(t_i)$, be observations of a Markov process, so that (ignoring the contribution of $x_1$) the likelihood is

$$\pi(x \mid \theta) = \prod_{i=2}^n \pi(x_i \mid x_{i-1}, \theta).$$

**Factorisation (Eq. 2).** With

$$\varphi_i(\theta) = \frac{\pi(x_i \mid x_{i-1},\theta)\,\pi(\theta)}{\int \pi(x_i \mid x_{i-1},\vartheta)\,\pi(\vartheta)\,d\vartheta},$$

the posterior given one transition started at $x_{i-1}$, one has

$$\pi(\theta \mid x) \;\propto\; \pi(\theta)^{2-n}\prod_{i=2}^n \varphi_i(\theta).$$

**Piecewise ABC (PW-ABC).** For each $i$, draw $\theta^* \sim \pi$, simulate $y_i \sim \pi(\cdot \mid x_{i-1},\theta^*)$ and accept if $\|y_i - x_i\| \le \varepsilon$; the accepted draws sample an ABC approximation $\varphi_i^{\varepsilon}$ of $\varphi_i$, with no summary statistic needed because each factor involves a single data point. Estimate each factor density, multiply, multiply by $\pi(\theta)^{2-n}$, and normalise.

**Gaussian product rule.** If each factor is approximated by $\mathcal N(\hat\mu_i, Q_i)$ (sample mean and covariance of its ABC sample), the product is proportional to $\mathcal N(a, B)$ with

$$B^{-1} = \sum_{i=2}^n Q_i^{-1}, \qquad a = B\sum_{i=2}^n Q_i^{-1}\hat\mu_i.$$

With a Gaussian prior $\mathcal N(\mu_{pri}, \Sigma_{pri})$ the PW-ABC posterior is Gaussian with precision $B^{-1} - (n-2)\Sigma_{pri}^{-1}$ and mean $\big(B^{-1} - (n-2)\Sigma_{pri}^{-1}\big)^{-1}\big(B^{-1}a - (n-2)\Sigma_{pri}^{-1}\mu_{pri}\big)$, provided that precision matrix is positive definite. If instead each factor is estimated by the Gaussian kernel density estimate $\hat\varphi_i$ (source Eq. (12)) from its $m$ accepted draws, with bandwidth matrix $H_i = q\,m^{-2/(d+4)}Q_i$ ($q > 0$ fixed, $d$ the dimension of $\theta$), then, under the regularity conditions of Wand and Jones (1995) on each $\varphi_i^{\varepsilon}$, the bias, variance and mean integrated squared error of $\prod_i\hat\varphi_i$ as an estimator of $\prod_i\varphi_i^{\varepsilon}$ are $o(1)$ as $m \to \infty$ with $n$ fixed.

**Implied likelihood.** Standard ABC with an $L_p$ ball of radius $\varepsilon$ replaces the likelihood by its average over one ball in the joint data space, while PW-ABC replaces each transition density by its average over a ball around $x_i$; the PW-ABC likelihood is the product of these per-transition averages.

## Expansion

By Bayes' theorem $\pi(x_i \mid x_{i-1},\theta) = \varphi_i(\theta)\,c_i/\pi(\theta)$ with $c_i$ free of $\theta$. Substituting into the Markov likelihood and multiplying by the prior gives $\pi(\theta)\prod_{i=2}^n \varphi_i(\theta)/\pi(\theta) = \pi(\theta)^{1-(n-1)}\prod_i \varphi_i(\theta)$, which is the stated factorisation. The Gaussian formulas follow from adding precisions and precision-weighted means of Gaussian densities; the prior appears with exponent $2-n$, hence the subtracted term. Each Gaussian factor is the Kullback–Leibler-optimal Gaussian approximation of its target, but the normalised product of these approximations need not be the best Gaussian approximation of the product, which motivates the kernel estimator.

## Sources

- S. R. White, T. Kypraios, S. P. Preston, "Piecewise Approximate Bayesian Computation: fast inference for discretely observed Markov models using a factorised posterior distribution", Statistics and Computing (2015), Section 2, Eqs. (1)–(3), (6)–(11), (19)–(21) and (25)–(28), <https://doi.org/10.1007/s11222-013-9432-2>, PMCID PMC4470364.
