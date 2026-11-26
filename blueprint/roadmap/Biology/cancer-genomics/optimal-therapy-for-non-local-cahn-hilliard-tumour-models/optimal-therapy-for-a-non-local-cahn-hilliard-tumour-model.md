# Optimal therapy for a non-local Cahn-Hilliard tumour model via maximal regularity

**Model.** On a bounded smooth domain $\Omega\subset\mathbb{R}^N$ ($N\le3$) over $Q_T=\Omega\times(0,T)$, let $\phi$ be the tumour phase variable ($\phi=1$ tumour, $\phi=-1$ healthy tissue), $\mu$ its chemical potential and $\sigma$ the nutrient concentration. The non-local Cahn-Hilliard-reaction-diffusion system with therapies is

$$\partial_t\phi-\Delta\mu=P(\phi)(\sigma-\mu)-h(\phi)\,u,\qquad \mu=AF'(\phi)+Ba\,\phi-BJ*\phi,\qquad \partial_t\sigma-\Delta\sigma=-P(\phi)(\sigma-\mu)+v,$$

with homogeneous Neumann conditions $\partial_n\mu=\partial_n\sigma=0$ and initial data $\phi_0,\sigma_0$. Here $F$ is a regular double-well potential, $J$ a symmetric interaction kernel with $a=J*1$ (non-local cell-cell adhesion), $P\ge0$ a proliferation function, $h$ a bounded nonnegative function with $u$ a cytotoxic drug or radiotherapy control, and $v$ a nutrient supply control. (A chemotaxis coupling $\chi$ is also allowed for the local well-posedness.)

**Theorem (well-posedness).**

1. For $p>N+2$ and $\phi_0,\sigma_0$ in the trace space $W^{2-2/p,p}$ (with compatible Neumann data), the system has a unique maximal regular solution in weighted $L^p$ maximal-regularity classes, which either exists on $[0,T]$ or blows up in $W^{2-2/p,p}$.
2. Without chemotaxis and for bounded controls $u,v\in L^\infty(Q_T)$, weak solutions are uniformly bounded (Alikakos-Moser iteration) and Hölder continuous, and the maximal solution is global.
3. If $\phi_0,\sigma_0\in H^2(\Omega)$ satisfy the compatibility conditions $\partial_n(AF'(\phi_0)+Ba\phi_0-BJ*\phi_0)=0$ and $\partial_n\sigma_0=0$, there is a unique solution with

$$\phi,\mu,\sigma\in W^{1,6}(0,T;L^6(\Omega))\cap C^0([0,T];W^{1,6}(\Omega))\cap L^6(0,T;W^{2,6}(\Omega)),$$

bounded in this norm by a constant depending only on the data, and depending Lipschitz-continuously on the controls.

**Theorem (optimal control).** For the tracking-type cost

$$\mathcal{J}=\frac{\alpha_\Omega}{2}\|\phi(T)-\phi_\Omega\|^2_{L^2(\Omega)}+\frac{\alpha_Q}{2}\|\phi-\phi_Q\|^2_{L^2(Q_T)}+\frac{\beta_\Omega}{2}\|\sigma(T)-\sigma_\Omega\|^2_{L^2(\Omega)}+\frac{\beta_Q}{2}\|\sigma-\sigma_Q\|^2_{L^2(Q_T)}+\frac{\alpha_u}{2}\|u\|^2_{L^2(Q_T)}+\frac{\beta_v}{2}\|v\|^2_{L^2(Q_T)}$$

over box constraints $u_{\min}\le u\le u_{\max}$, $v_{\min}\le v\le v_{\max}$, an optimal therapy $(\bar u,\bar v)$ exists. The control-to-state map is Fréchet differentiable, and $(\bar u,\bar v)$ satisfies first-order necessary conditions expressed through the unique solution of a linear backward adjoint system: a variational inequality that reduces to a pointwise projection of the adjoint-weighted gradient onto the admissible box when $\alpha_u,\beta_v>0$.

## Expansion

1. The system is rewritten as a quasilinear parabolic problem for $(\phi,\sigma)$ with inhomogeneous Robin-type boundary conditions; Meyries-Schnaubelt maximal regularity in time-weighted $L^p$ spaces gives local existence and uniqueness of regular solutions.
2. Energy estimates plus Alikakos-Moser iteration give $L^\infty$ bounds on weak solutions, and parabolic Hölder regularity then rules out blow-up, so the maximal solution is global.
3. The direct method with the $W^{1,6}$-$W^{2,6}$ bounds gives an optimal control; linearizing around the optimal state and introducing adjoint variables yields the optimality system.

## Sources

- M. Fornoni, *Maximal regularity and optimal control for a non-local Cahn-Hilliard tumour growth model*, arXiv:2402.04204 (Theorem 3.10, Theorems 4.7, 4.8 and 4.11, Theorems 5.2, 5.5, 5.7 and 5.9). <https://doi.org/10.48550/arXiv.2402.04204> Published version: Journal of Differential Equations 410 (2024) 382–448, <https://doi.org/10.1016/j.jde.2024.07.036>.
