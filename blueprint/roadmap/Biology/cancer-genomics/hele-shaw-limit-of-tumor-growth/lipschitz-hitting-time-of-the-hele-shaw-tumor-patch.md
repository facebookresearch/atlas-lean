# Lipschitz hitting time of the Hele-Shaw tumor patch

**Model.** A tumor occupying the patch $\Omega_t = \{p(\cdot,t) > 0\} \subset \mathbb{R}^d$ grows by the incompressible (Hele-Shaw) limit of a porous-medium cell-density model,

$$\partial_t\rho - \nabla\cdot(\rho\nabla p) = c\rho, \qquad 0 \le \rho \le 1, \qquad p(1-\rho) = 0,$$

with patch data $\rho(\cdot,0) = \chi_{\Omega_0^+}$. For patch solutions this is the Hele-Shaw flow with source,

$$-\Delta p = c \ \text{ in } \{p>0\}, \qquad V = |\nabla p| \ \text{ on } \partial\{p>0\},$$

where $V$ is the outward normal velocity of the free boundary (Darcy's law). In the tumor model with nutrients the source is the nutrient concentration, consumed by the tumor: $\partial_t c - \Delta c = -c\rho$. Let $T(x) = \inf\{t : x \in \Omega_t\}$ be the **hitting time** of the point $x$ by the patch.

**Hypotheses.** (A1) $c \ge 0$ is continuous, bounded above and below by positive constants on every $\mathbb{R}^d\times[0,\tau]$, and Lipschitz in $x$; (A2) $\Omega_0^+$ is bounded; (IB) $\Omega_0^+$ satisfies a uniform interior ball condition of radius $r_0 > 0$; and $(\partial_t c)^- \in L^1_{\mathrm{loc}}([0,\infty); L^\infty(\mathbb{R}^d))$.

**Theorem.**
1. (General source) Under these hypotheses, $\partial\{p>0\} = \{(x,T(x)) : x \in O\}$ with $O = T^{-1}((0,\infty))$, and $T$ is continuous. For each $\tau > 0$ there are $L < \infty$ and $\varepsilon > 0$ depending only on $d$, $r_0$, $\tau$, $\inf c$, $\|\nabla_x c\|_\infty$ and $\|(\partial_t c)^-\|_{L^1L^\infty}$ such that
$$|T(x) - T(y)| \le L|x-y| \qquad \text{whenever } \min\{T(x),T(y)\} < \tau,\ |x-y| < \varepsilon.$$
Moreover the pressure is linearly nondegenerate: $\sup_{B_r(x)} p(\cdot,t) \ge \kappa r$ for $x \in \partial\Omega_t$, $0<t<\tau$, $0<r<r_*$.
2. (Tumor model) Let $d \in \{1,2,3\}$ and let $(\rho,p,c)$ be a patch solution of the density-nutrient system with $\Omega_0^+$ bounded and satisfying (IB), and $c_0 \in W^{2,\infty}(\mathbb{R}^d)$ with $\inf c_0 > 0$. Then the nutrient satisfies all the source hypotheses, so the tumor's hitting time is locally Lipschitz on $\{T < \infty\}$.
3. (No-collision times) If at time $t_0$ the patch has no collision-type singular points, then on a time interval around $t_0$, $T$ is $C^1$, the space-time free boundary is a $C^1$ hypersurface, and its singular points are exactly the points where $\nabla T = 0$, i.e. where the normal velocity of the patch diverges.

## Expansion

Because $V = |\nabla T|^{-1}$, a Lipschitz bound on $T$ is a quantitative lower bound on the expansion speed of the tumor boundary, valid at singular points too. It is optimal: where two lobes of the tumor collide, $T$ is locally the minimum of two smooth functions. The proof combines the interior ball condition (no inward cusps) with a Hopf-Lax type inequality for the pressure and nondegeneracy barriers; for the tumor model, the sharp $L^4$ estimate of $\nabla p$ fed into heat-semigroup smoothing bounds $(\partial_t c)^-$, and the resulting time singularity is integrable exactly when $d \le 3$. At hole closings (lower-dimensional singular strata) the patch velocity blows up and $\nabla T$ vanishes.

## Sources

- Carson Collins, Inwon Kim and Sebastian Munoz, "Space-time geometry of Hele-Shaw flow", arXiv:2608.16509 (2026), Section 1, Theorems 1.1, 1.6 and 1.7, <https://doi.org/10.48550/arXiv.2608.16509>.
