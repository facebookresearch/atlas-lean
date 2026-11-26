# Local ε-regularity for the chemotaxis–Stokes system with signal consumption

**Setting.** Bacterial density $n$, oxygen concentration $c$, fluid velocity $u$ and pressure $\pi$ satisfy, in $\mathbb{R}^3$,

$$n_t + u\cdot\nabla n = \Delta n - \nabla\cdot(n\nabla c), \qquad c_t + u\cdot\nabla c = \Delta c - nc, \qquad u_t - \Delta u + \nabla\pi = nF,\ \ \nabla\cdot u = 0,$$

with a prescribed gravitational potential force $F = \nabla\Phi$.
For $z_0 = (t_0,x_0)$ let $Q_r(z_0) = (t_0 - r^2, t_0)\times B_r(x_0)$ and define the scale-invariant quantities

$$\mathcal{A}_p(r;z_0) = r^{2p-5}\iint_{Q_r(z_0)} n^p, \qquad U(r;z_0) = \|u\|_{L^5(Q_r(z_0))}, \qquad P(r;z_0) = \|\pi - (\pi)_{B_r}(t)\|_{L^2_tL^3_x(Q_r(z_0))},$$

where $(\pi)_{B_r}(t)$ is the spatial mean of $\pi(t,\cdot)$ over $B_r(x_0)$.

**Theorem (ε-regularity).** Let $0 \le G < \infty$ and $3/2 < p \le 5/3$. There are $\varepsilon_* = \varepsilon_*(A,G,p) > 0$ and $C = C(A,G,p)$ such that: if the system holds classically in $Q_R(z_0)$ with $n > 0$, $0 \le c \le A$ and $R\|F\|_\infty \le G$, and

$$\mathcal{A}_p(R;z_0) + U(R;z_0) + P(R;z_0) \le \varepsilon_*,$$

then

$$\sup_{Q_{R/2}(z_0)}\big(n + |\nabla c|^2 + |u|^2\big) \le C R^{-2}.$$

No smallness of $\nabla c$ is assumed: the signal amplitude $A$ is arbitrary, and the constants do not depend on upper or positive lower bounds for $n$.

## Expansion

The proof combines a joint local entropy for $n\log n$ coupled with the Fisher information $|\nabla\sqrt c|^2$ and a fixed-scale energy for the velocity, in the spirit of the Caffarelli–Kohn–Nirenberg partial regularity theory for Navier–Stokes. A heat-kernel decomposition of $c$ shows that smallness of the density and velocity quantities already forces the signal gradient to be small at smaller scales, so the gradient need not appear in the hypothesis. An iteration over shrinking cylinders then gives decay of the scale-invariant quantities and the pointwise bound.

## Sources

- F. Shi, W. Wang and G. Yang, "Global regularity for the chemotaxis–Stokes system with signal consumption in $\mathbb{R}^3$", arXiv:2609.35204 (2026), Theorem 1.8 and Remark 1.9, proved in Section 3, <https://doi.org/10.48550/arXiv.2609.35204>.
