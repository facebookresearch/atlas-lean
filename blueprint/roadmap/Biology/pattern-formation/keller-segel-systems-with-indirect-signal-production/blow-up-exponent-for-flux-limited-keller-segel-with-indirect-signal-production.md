# Blow-up exponent for flux-limited Keller–Segel with indirect signal production

**Model.** In a smooth bounded domain $\Omega \subset \mathbb R^N$ with homogeneous Neumann conditions, cells $u$ diffuse with a nonlinear diffusivity $D(u)$ and move up the gradient of a signal $v$ with a flux-limited sensitivity, while the signal is produced indirectly through an intermediate substance $w$ secreted by the cells:
$$u_t = \nabla\cdot\big(D(u)\nabla u\big) - \nabla\cdot\big(u\,(1+|\nabla v|^2)^{\sigma}\nabla v\big),\qquad 0 = \Delta v - v + w,\qquad w_t = -w + u,$$
with $D>0$ on $[0,\infty)$ and $D(\xi) \simeq \xi^{m-1}$ as $\xi\to\infty$ ($\sigma<0$ limits the chemotactic flux). Initial data $(u_0,w_0) \in C^1(\overline\Omega)^2$ are non-negative.

**Theorem (global existence and boundedness).** Suppose $D(\xi) \ge k_D\,\xi^{m-1}$ for large $\xi$.

- If $N = 1$, $m \ge 0$ and $\sigma \in \mathbb R$, the classical solution is global, and bounded if $m>0$.
- If $N \ge 2$, $m > 1 - \frac1N$ and $\sigma \le \frac{mN+2-2N}{2N-2}$, the classical solution is global; it is uniformly bounded if $\sigma < \frac{mN+2-2N}{2N-2}$.

**Theorem (finite-time blow-up).** Let $\Omega = B_R(0)$ and suppose $D \in C^3$ with $D(\xi) \le K_D\,\xi^{m-1}$ for large $\xi$, where $m < 2 - \frac2N$ and
$$\sigma > \max\Big\{\frac{N}{2-2N},\ \frac{mN+2-2N}{2N-2}\Big\} \quad (N\ge2), \qquad \sigma \in \mathbb R \quad (N=1).$$
Then for every $T^*>0$ and $M^* > M_* > 0$ there are radial profiles $M^{(u)}, M^{(w)}$ such that every radially symmetric initial datum with masses of $u_0$ and $w_0$ in $[M_*,M^*]$ and sufficiently concentrated near the origin, $\int_{B_r}u_0 \ge M^{(u)}(r)$ and $\int_{B_r}w_0 \ge M^{(w)}(r)$ for all $r\in(0,R)$, blows up before $T^*$: $\limsup_{t\nearrow T_{\max}}\|u(\cdot,t)\|_{L^\infty} = \infty$ with $T_{\max} < T^*$. For $N=1$ this happens when $m<0$.

Thus $\sigma = \frac{mN+2-2N}{2N-2}$ is the critical exponent separating boundedness from blow-up in the range where both statements apply.

## Expansion

Global existence follows from $L^p$ energy estimates in which diffusion $\sim u^{m-1}$ must dominate the flux-limited cross-diffusion; the elliptic and ODE equations give $\|\nabla v\|$ control in terms of past values of $u$, and the exponent balance produces the threshold in $\sigma$. Blow-up uses the radial mass accumulation function $U(s,t) = \int_0^{s^{1/N}}\rho^{N-1}u(\rho,t)\,d\rho$, which satisfies a degenerate parabolic inequality; comparison with explicit subsolutions forces $U_s$ to become unbounded at the origin in finite time.

## Sources

- Yue Zhou and Changchun Liu, "Boundedness and blow-up for a quasilinear Keller-Segel system with flux limitation and indirect signal production", arXiv:2607.07130 (2026), Theorems 1.1 (blow-up) and 1.2 (global existence and boundedness), <https://doi.org/10.48550/arXiv.2607.07130>.
