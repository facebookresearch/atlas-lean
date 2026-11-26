# Global solvability with arbitrary mass for a volume-filling Keller–Segel–Navier–Stokes system near Couette flow

**Model.** On $\mathbb{T}\times\mathbb{R}$, cell density $n \ge 0$, chemoattractant $c$ and fluid velocity $u$ with pressure $p$ satisfy the Patlak–Keller–Segel–Navier–Stokes system

$$\partial_t n + u\cdot\nabla n = \nabla\cdot\big((1+n)^{\alpha-1}[1 + (1-\alpha)n]\nabla n\big) - \nabla\cdot\big(n(1+n)^\alpha\nabla c\big), \qquad \Delta c + n - c = 0,$$

$$\partial_t u + u\cdot\nabla u + \nabla p = \Delta u + n e_2, \qquad \nabla\cdot u = 0,$$

with $0 < \alpha < 1$. The coefficients follow the Painter–Hillen constitutive relation $\phi(n) = Q(n) - nQ'(n)$, $\psi(n) = nQ(n)$ for diffusion $\phi$ and sensitivity $\psi$, with $Q(n) = (1+n)^\alpha$: the sensitivity grows like $n^{1+\alpha}$, between linear and quadratic, and diffusion grows like $(1-\alpha)n^\alpha$. Buoyancy $ne_2$ couples cells to the fluid. The base flow is the Couette flow $(Ay,0)$ with $A \ge 1$.

**Theorem.** Let $0 < \alpha < 1$, $0 \le n_{\mathrm{in}} \in L^1\cap H^3(\mathbb{T}\times\mathbb{R})$ with mass $M = \int n_{\mathrm{in}}$, and a divergence-free perturbation $v_{\mathrm{in}} \in H^3$. There is $A_0 \ge 1$, depending only on $\alpha$, $M$, $\|n_{\mathrm{in}}\|_{H^3}$ and $\|v_{\mathrm{in}}\|_{H^3}$, such that for every $A \ge A_0$ the system with $u_{\mathrm{in}} = (Ay,0) + v_{\mathrm{in}}$ has a unique global classical solution; the perturbation $(n, v)$ lies in $C([0,T];H^3)\cap L^2(0,T;H^4)$ for every finite $T$; the density stays nonnegative and conserves its mass; and

$$\sup_{t\ge0}\big(\|n(t)\|_{L^2} + \|n(t)\|_{L^\infty} + \|\omega_{\neq}(t)\|_{L^2} + \|\omega_0(t)\|_{L^\infty(\mathbb{R})}\big) \le C\big(\alpha, M, \|n_{\mathrm{in}}\|_{H^3}, \|v_{\mathrm{in}}\|_{H^3}\big),$$

where $\omega = \partial_y v_1 - \partial_x v_2$ is the perturbation vorticity, with $x$-average $\omega_0$ and non-zero modes $\omega_{\neq}$. No smallness of the cell mass is required.

## Expansion

After rescaling time by $A$, the equations become a transport by $y\partial_x$ with $A^{-1}$-small diffusion. Non-zero $x$-modes undergo enhanced dissipation at the scale $A^{-1/3}$, captured by bounded (arctangent-type) Fourier-multiplier corrections inside a joint energy for the full density and the non-zero-mode vorticity; estimating the full density (rather than its zero and non-zero modes separately) keeps the positive nonlinear diffusion and avoids mixed terms of indefinite sign. The $x$-averaged density $n_0$ is not mixed, but it is a one-dimensional function, and because $\alpha < 1$ one-dimensional interpolation absorbs its chemotactic production $n^{1+\alpha}$ into the diffusion for every finite mass.

## Sources

- L. Wang, "Global solvability with arbitrary mass for a chemotaxis–fluid model with sensitivity growth between linear and quadratic", arXiv:2610.19453 (2026), Theorem 1.1 with Proposition 1.1 and Remark 1.1, <https://doi.org/10.48550/arXiv.2610.19453>.
