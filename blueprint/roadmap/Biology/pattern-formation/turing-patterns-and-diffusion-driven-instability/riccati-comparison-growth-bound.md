# Riccati comparison bound for growth of a second-order non-autonomous linear ODE

This page covers the comparison principle (Theorem 3.1 and its exponential corollary) that Van Gorder, Klika and Krause (2021) use to replace eigenvalue criteria for linear stability on time-dependent domains.

Let $I = [t_0, t_1)$ with $0 \le t_0 < t_1 \le \infty$, let $F, G \in C(I)$, and consider

$$\ddot Y + F(t)\, \dot Y + G(t)\, Y = 0 . \qquad (18)$$

**Theorem (comparison; Theorem 3.1).** Let $\Phi \in C^2(I)$ with $\Phi(t) > 0$ on $I$. If

$$G(t) \le -\frac{\ddot \Phi}{\Phi} - \frac{\dot \Phi}{\Phi} F(t) \quad \text{for all } t \in I,$$

then the solution of (18) with $Y(t_0) = \Phi(t_0)$, $\dot Y(t_0) = \dot\Phi(t_0)$ satisfies $Y(t) \ge \Phi(t) > 0$ for all $t \in I$.

**Corollary (exponential growth at a fixed rate).** Let $\mu \in C^2(I)$ be positive and fix $\delta > 0$. If

$$G(t) \le -\frac{\ddot \mu}{\mu} - \Big(\frac{\dot \mu}{\mu} + \delta\Big) F(t) - 2\delta\frac{\dot\mu}{\mu} - \delta^2 \quad \text{for all } t \in I,$$

then (18) has a solution with $Y(t) \ge \mu(t)\, e^{\delta t}$, i.e. $Y(t)/\mu(t) \ge e^{\delta t}$, on $I$.

The exponent $\delta > 0$ is fixed: the strict pointwise inequality $G < -\ddot\mu/\mu - (\dot\mu/\mu) F$ obtained by letting $\delta \to 0^+$ is not a uniform positive margin and does not give exponential growth. For example, with $\mu = 1$, $F = 0$ and $G = -2/(1+t)^2$ on $[0, \infty)$ it holds, yet every solution is a combination of $(1+t)^2$ and $(1+t)^{-1}$. Nor is there a decay converse: with $\mu = 1$, $F = -3$ and $G = 2$ the reverse inequality $G > -\ddot\mu/\mu - (\dot\mu/\mu) F = 0$ holds while $Y = e^{2t}$ solves (18).

Eigenvalues of a time-dependent coefficient matrix predict neither stability nor instability of a non-autonomous system, which is why a criterion of this differential-inequality form is used. When $F$, $G$ and $\mu$ are constant, the corollary's condition reads $\delta^2 + F\delta + G \le 0$: the characteristic polynomial $s^2 + Fs + G$ is nonpositive at $s = \delta$, so it has a real root at least $\delta$.

## Expansion

As long as $Y > 0$, $Z = \dot Y / Y$ solves the Riccati equation $\dot Z = -Z^2 - FZ - G$. The function $Z_1 = \dot\Phi/\Phi$ satisfies $\dot Z_1 = \ddot\Phi/\Phi - Z_1^2 \le -Z_1^2 - FZ_1 - G$ by the hypothesis, so it is a subsolution with the same initial value $Z(t_0) = Z_1(t_0)$, and the comparison theorem for scalar ODEs gives $Z \ge Z_1$ forward in time. Since $\dot Z \le -Z^2 + |F||Z| + |G|$, $Z$ cannot blow up to $+\infty$, and it stays above $Z_1$, so $Y$ never vanishes on $I$; integrating $Z \ge Z_1$ from $t_0$ gives $Y/\Phi \ge 1$. The corollary is the theorem with $\Phi = \mu e^{\delta t}$, for which $\dot\Phi/\Phi = \dot\mu/\mu + \delta$ and $\ddot\Phi/\Phi = \ddot\mu/\mu + 2\delta\dot\mu/\mu + \delta^2$.

## Sources

- R. A. Van Gorder, V. Klika and A. L. Krause, Turing conditions for pattern forming systems on evolving manifolds, *J. Math. Biol.* (2021), Section 3.1, <https://doi.org/10.1007/s00285-021-01552-y>; preprint <https://arxiv.org/abs/1904.09683> (theorem and equation numbers follow the preprint; the corollary here fixes the rate $\delta$ rather than taking the preprint's limit $\delta \to 0^+$).
