# The AIPW remainder is bounded by a product of $L^2$ nuisance errors

Let $(\Omega, \mathcal{F}, \mu)$ be a finite measure space, $m$ a σ-algebra on $\Omega$, $T \in \mathcal{F}$, and $Y_0, Y_1 \in L^2(\mu)$. Write $e^* = \mu[\mathbf{1}_T \mid m]$ and $\mu_a^* = \mu[Y_a \mid m]$. Let $e$ be an almost everywhere strongly measurable function and $g_0, g_1 \in L^2(\mu)$, and suppose that for some $\varepsilon > 0$,

$$\varepsilon \le e \le 1 - \varepsilon \quad \mu\text{-a.e.}$$

Then the AIPW remainder $R(e, g_0, g_1) = \int (e^* - e)\bigl((\mu_1^* - g_1)/e + (\mu_0^* - g_0)/(1 - e)\bigr)\, d\mu$ satisfies

$$\lvert R(e, g_0, g_1) \rvert \le \varepsilon^{-1} \sqrt{\int (e^* - e)^2 \, d\mu}\,\left(\sqrt{\int (\mu_1^* - g_1)^2 \, d\mu} + \sqrt{\int (\mu_0^* - g_0)^2 \, d\mu}\right).$$

The bound is second order: a product of the $L^2$ propensity error and the $L^2$ outcome-regression errors.

Here $\mu[f \mid m]$ is the conditional expectation of $f$ given $m$ when $m$ is contained in $\mathcal{F}$, $\mu$ restricted to $m$ is σ-finite and $f$ is integrable, and it is $0$ otherwise. Only in the first case are $e^*$ and $\mu_a^*$ the actual propensity and outcome regressions; the statement covers the other cases with these zero values.
