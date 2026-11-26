# Subcritical-mass global generalized solutions of the doubly degenerate Keller–Segel system

**Model.** Let $\Omega \subset \mathbb{R}^2$ be a smoothly bounded domain. Cell density $u$ and signal concentration $v$ satisfy
$$u_t = \nabla\cdot(uv\nabla u) - \nabla\cdot(u^2v\nabla v), \qquad v_t = \Delta v + u - v,$$
with no-flux conditions $(uv\nabla u - u^2v\nabla v)\cdot\nu = \nabla v\cdot\nu = 0$ on $\partial\Omega$. The initial data satisfy only $u_0, v_0 \in W^{1,\infty}(\Omega)$, $u_0 \ge 0$, $u_0 \not\equiv 0$, $v_0 \ge 0$: both may vanish on large parts of $\Omega$, so the diffusion may be degenerate from the start.

**Theorem.** Suppose that either
1. $\int_\Omega u_0 < 4\pi$, or
2. $\Omega = B_R(0)$, $u_0$ and $v_0$ are radially symmetric, and $\int_\Omega u_0 < 8\pi$.

Then there is a global generalized energy solution $(u,v)$ with $u \ge 0$, $v > 0$ for $t > 0$, $u \in C^0(\overline\Omega\times(0,\infty)) \cap L^2_{loc}((0,\infty);W^{1,2}(\Omega))$ and $v \in C^{2,1}(\overline\Omega\times(0,\infty)) \cap L^\infty((0,\infty);W^{1,2}(\Omega))$. It conserves mass, $\int_\Omega u(\cdot,t) = \int_\Omega u_0$, has bounded entropy $\sup_{t>0}\int_\Omega u\ln u < \infty$, attains the signal datum in the sense $v(\cdot,t) \to v_0$ in every $L^p$, $p < \infty$, and in case 2 is radially symmetric. Here a generalized energy solution satisfies the signal equation weakly, conserves mass, obeys the energy inequality
$$\mathcal{F}(u(t),v(t)) + \int_0^t\!\!\int_\Omega v_t^2 + \int_0^t\!\!\int_\Omega \big|\sqrt v\,\nabla u - u\sqrt v\,\nabla v\big|^2 \le \mathcal{F}(u_0,v_0), \qquad \mathcal{F}(u,v) = \int_\Omega u\ln u - \int_\Omega uv + \frac12\int_\Omega|\nabla v|^2 + \frac12\int_\Omega v^2,$$
for almost every $t$, and satisfies a family of supersolution inequalities for renormalizations $f_\lambda(u)$ of the cell equation.

## Expansion

Despite the degenerate diffusion, the classical Keller–Segel functional $\mathcal{F}$ is still nonincreasing along regularized solutions (with positive perturbations of the initial data). Combined with the Moser–Trudinger inequality, $\mathcal{F}$ is bounded below when the mass is below $4\pi$, or below $8\pi$ for radial data, yielding time-global bounds for $\int u\ln u$ and $\|v\|_{W^{1,2}}$. Higher regularity needs a positive lower bound for $v$, available only away from $t = 0$, so estimates are derived on $(\tau,\infty)$ and the limit is identified in the weak energy sense. The thresholds $4\pi$ and $8\pi$ are the critical masses of the classical two-dimensional Keller–Segel system for general and radial data.

## Sources

- T. Black and G. Li, "Subcritical-mass global solvability in a doubly degenerate Keller–Segel system with signal production", arXiv:2607.04649 (2026), Theorem 1.1 and the definition of generalized energy solutions (Section 6), with the Lyapunov-functional estimates of Section 3, <https://doi.org/10.48550/arXiv.2607.04649>.
