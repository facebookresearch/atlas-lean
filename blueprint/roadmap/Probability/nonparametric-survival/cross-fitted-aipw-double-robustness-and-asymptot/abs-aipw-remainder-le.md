# The remainder is bounded by a product of `L²` nuisance errors

Let $(\Omega, \mathcal{F}, \mu)$ be a finite measure space, $m$ a σ-algebra on $\Omega$, $T \in \mathcal{F}$, and $Y_0, Y_1 \in L^2(\mu)$. Write $e^* = \mu[\mathbf{1}_T \mid m]$ and $\mu_a^* = \mu[Y_a \mid m]$. Let $e$ be an almost everywhere strongly measurable function and $g_0, g_1 \in L^2(\mu)$, and suppose that for some $\varepsilon > 0$,

$$\varepsilon \le e \le 1 - \varepsilon \quad \mu\text{-a.e.}$$

Then the AIPW remainder $R(e, g_0, g_1) = \int (e^* - e)\bigl((\mu_1^* - g_1)/e + (\mu_0^* - g_0)/(1 - e)\bigr)\, d\mu$ satisfies

$$\lvert R(e, g_0, g_1) \rvert \le \varepsilon^{-1} \sqrt{\int (e^* - e)^2 \, d\mu}\,\left(\sqrt{\int (\mu_1^* - g_1)^2 \, d\mu} + \sqrt{\int (\mu_0^* - g_0)^2 \, d\mu}\right).$$

The bias is second order: a product of the propensity error and the outcome-regression errors.
