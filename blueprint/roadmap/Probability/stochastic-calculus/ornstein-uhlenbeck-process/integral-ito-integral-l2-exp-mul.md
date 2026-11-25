# Covariance of the Wiener integrals

Let $B$ be a pre-Brownian motion adapted to a filtration $F$, with increments $B_t - B_s$ ($s \le t$)
independent of $F_s$, and $\theta \ne 0$. Then the Wiener integrals $I_t = \int_0^t e^{\theta u}\, dB_u$ (the
[$L^2$ Itô integrals](../it-integral/ito-integral-l2.md) of the deterministic integrand $e^{\theta u}$) satisfy, for all
$s, t \ge 0$,

$$\mathbb E[I_s I_t] = \frac{e^{2\theta \min(s, t)} - 1}{2\theta},$$

by the martingale property and the Itô isometry.
