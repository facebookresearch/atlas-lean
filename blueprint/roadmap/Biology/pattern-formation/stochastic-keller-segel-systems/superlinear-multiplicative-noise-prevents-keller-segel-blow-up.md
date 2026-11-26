# Superlinear multiplicative noise prevents Keller-Segel blow-up

**Model.** On a smooth bounded domain $D \subset \mathbb{R}^d$ with homogeneous Neumann conditions, consider the Keller-Segel system with pointwise multiplicative Itô noise driven by one real Brownian motion $W$:

$$du = \big[\Delta u - \chi\nabla\cdot(u\nabla v)\big]\,dt + \sigma_0u^r\,dW_t, \qquad \tau\partial_t v = \Delta v - v + u,$$

with $\chi > 0$, $\sigma_0 > 0$, $r > 1$, and either $\tau = 0$ (parabolic-elliptic) or $\tau > 0$ (fully parabolic). In the deterministic case $\sigma_0 = 0$ solutions can blow up in finite time (e.g. in $d = 2$ above the critical mass).

**Theorem.**
1. ($r > 3/2$) For every $d \ge 1$, every $\sigma_0 > 0$ and both $\tau = 0$ and $\tau > 0$, there is a pathwise unique global nonnegative mild solution. For each $T < \infty$ and $\lambda \in (0,1)$, $\mathbb{P}\big(\sup_{0\le t\le T}\|u(t)\|_\infty \ge R\big) \le C_{T,\lambda}(1+R)^{-\lambda}$ in the parabolic-elliptic case, and $\mathbb{E}\big[\sup_{t\le T}\|u(t)\|_\infty^s\big] < \infty$ for every $s \in (0,1)$.
2. ($r = 3/2$) If $\tau = 0$ and $\sigma_0^2 \ge 2\chi$, there is a pathwise unique global nonnegative mild solution in every dimension, with

$$\mathbb{P}\Big(\sup_{0\le t\le T}\|u(t)\|_\infty \ge R\Big) \le \frac{\log(1+U_0) + \chi T}{\log(1+R)}, \qquad U_0 = 1 + \|u_0\|_\infty < R.$$

If $d = 2$, both systems are globally well posed for every $\sigma_0 > 0$.
3. (Mass extinction) For any global nonnegative mild solution with $r > 1$, $\|u(t)\|_{L^1} \to 0$ and $\|v(t)\|_{L^1} \to 0$ almost surely, $\int_0^\infty M(t)^{2r}\,dt < \infty$ almost surely, where $M(t) = \|u(t)\|_{L^1}$, and $\mathbb{E}\big[\sup_{t\ge0}M(t)^s\big] \le M_0^s/(1-s)$ for $s \in (0,1)$.

## Expansion

Integrating the equation over $D$ removes the transport terms, so the mass is a nonnegative local martingale, $dM = \sigma_0\big(\int u^r\big)dW$, which converges almost surely; its quadratic variation $\sigma_0^2\int_0^\infty(\int u^r)^2dt$ is then finite, and Jensen's inequality bounds $(\int u^r)^2$ below by a multiple of $M^{2r}$, forcing $M \to 0$. Heuristically, pointwise, Itô's formula for $\log(1+u)$ gives a drift $-\frac{\sigma_0^2}{2}u^{2r}/(1+u)^2$ that beats the chemotactic growth $\chi u^2$ at large $u$ exactly when $2r - 2 > 1$, or when $r = 3/2$ and $\sigma_0^2 \ge 2\chi$; comparing the local solution with a scalar SDE then rules out explosion. In the fully parabolic case a logarithmic estimate on $(v_t)_-$ replaces the elliptic identity $\Delta v = v - u$.

## Sources

- Yunfeng Chen and Tusheng Zhang, "Global Well-posedness and Asymptotic Extinction for Keller-Segel Systems with Superlinear Noise", arXiv:2610.36485 (2026), Section 2, Theorems 2.2, 2.3 and 2.6, Corollary 2.5, <https://doi.org/10.48550/arXiv.2610.36485>.
