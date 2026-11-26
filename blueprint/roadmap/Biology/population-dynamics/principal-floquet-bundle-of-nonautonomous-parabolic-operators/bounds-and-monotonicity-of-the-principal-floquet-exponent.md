# Bounds and monotonicity of the principal Floquet exponent

**Setting.** Let $\Omega \subset \mathbb{R}^N$ be a bounded smooth domain, $A(x)$ a symmetric, uniformly elliptic $C^{2+\delta}$ matrix field, and $c \in C^{\delta,\delta/2}(\overline{\Omega}\times\mathbb{R})$ a bounded potential with $\sup_t [c(\cdot,t)]_{\delta;\Omega} < \infty$ (no periodicity in $t$ is assumed). For a frequency $\omega > 0$ and diffusion rate $d > 0$, the **normalized principal Floquet bundle** is the unique pair $(H,\varphi)$ with $H \in C(\mathbb{R})$ and

$$\omega\partial_t\varphi - d\,\operatorname{div}(A(x)\nabla\varphi) + c(x,t)\varphi = H(t)\varphi \quad \text{in } \Omega\times\mathbb{R},$$

$\mathbf{n}\cdot(A\nabla\varphi) = 0$ on $\partial\Omega\times\mathbb{R}$, $\varphi > 0$, and $\int_\Omega \varphi(x,t)\,dx = 1$ for every $t$. The **principal Floquet exponents** are the long-time averages

$$\underline{\lambda}_H(\omega,d) = \liminf_{T\to\infty}\frac{1}{T}\int_0^T H(s)\,ds, \qquad \overline{\lambda}_H(\omega,d) = \limsup_{T\to\infty}\frac{1}{T}\int_0^T H(s)\,ds.$$

For time-periodic $c$ they coincide with the periodic-parabolic principal eigenvalue; in general they differ. Let $\mathscr{C}$ be the set of uniform limits $\hat c$ of the time averages $\hat c_{T_n}(x) = \frac{1}{T_n}\int_0^{T_n} c(x,s)\,ds$ along sequences $T_n \to \infty$, and let $\mu^\infty(d,m)$ be the principal eigenvalue of $-d\,\operatorname{div}(A\nabla\phi) + m\phi = \mu\phi$ with Neumann boundary condition.

**Theorem.**
1. (Two-sided bounds) $\underline{\lambda}_H \le \inf_{\hat c\in\mathscr{C}}\mu^\infty(d,\hat c)$, $\overline{\lambda}_H \le \sup_{\hat c\in\mathscr{C}}\mu^\infty(d,\hat c)$, and
$$\liminf_{T\to\infty}\frac{1}{T}\int_0^T \min_{\overline{\Omega}} c(\cdot,s)\,ds \le \underline{\lambda}_H \le \liminf_{T\to\infty}\frac{1}{T}\int_0^T \frac{1}{|\Omega|}\int_\Omega c(x,s)\,dx\,ds,$$
with the analogous inequalities for $\overline{\lambda}_H$ using $\limsup$.
2. (Monotonicity) If $c_1 \ge c_2$ on $\Omega\times[t_0,\infty)$, then $\liminf_{T\to\infty}\frac{1}{T}\int_0^T [H(s;c_1)-H(s;c_2)]\,ds \ge 0$, hence $\underline{\lambda}_H(c_1) \ge \underline{\lambda}_H(c_2)$ and $\overline{\lambda}_H(c_1) \ge \overline{\lambda}_H(c_2)$; all three inequalities are strict if $\liminf_{T\to\infty}\frac{1}{T}\int_0^T\int_\Omega (c_1-c_2)\,dx\,ds > 0$.
3. (Asymptotic invariance) If $\|c_1(\cdot,t) - c_2(\cdot,t)\|_\infty \to 0$ as $t \to \infty$, the two potentials have the same exponents $\underline{\lambda}_H$ and $\overline{\lambda}_H$.

**Diffusion limits.** If, in addition, $c$ satisfies a uniform bound on the spatial derivatives of $\mathcal{M}(x,t;T) = t\hat c_T(x) - \int_0^t c(x,s)\,ds$ (true for finite sums of periodic functions), then for fixed $\omega$
$$\lim_{d\to 0}\underline{\lambda}_H(d) = \inf_{\hat c\in\mathscr{C}}\min_{\overline{\Omega}}\hat c, \qquad \lim_{d\to 0}\overline{\lambda}_H(d) = \sup_{\hat c\in\mathscr{C}}\min_{\overline{\Omega}}\hat c,$$
while as $d\to\infty$, for $c$ spatially heterogeneous on time average, the exponents converge to the $\liminf$ and $\limsup$ of the space-time average of $c$.

## Expansion

The lower bound comes from comparing $\varphi$ with the spatially constant solution of $\omega u' + \min_x c(x,t)\,u = H u$; the upper bounds come from integrating the equation against $\varphi$ or using the frozen-average eigenfunction of $\hat c$ as a sub-solution over long windows. A comparison principle tailored to long-time limits turns these sub/super-solutions into bounds on time averages of $H$, since $H$ itself is not monotone pointwise in $t$ (for periodic $c$, $H(t) = \lambda - \frac{d}{dt}\ln\int_\Omega w(x,t)\,dx$). Small diffusion localizes the bundle at the minimizers of the time-averaged potential, and large diffusion homogenizes it to the spatial mean. These exponents are the persistence thresholds of non-autonomous reaction-diffusion population models with growth rate $-c$.

## Sources

- Yun Li, Yuan Lou and Zhi-Cheng Wang, "Qualitative Properties of the Principal Floquet Bundle and Their Applications", arXiv:2609.26385 (2026), Chapter 1, Theorems 1.3 and 1.5, Remark 1.2, <https://doi.org/10.48550/arXiv.2609.26385>.
