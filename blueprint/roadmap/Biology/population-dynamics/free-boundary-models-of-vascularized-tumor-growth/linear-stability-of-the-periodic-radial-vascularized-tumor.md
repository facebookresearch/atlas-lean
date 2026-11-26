# Linear stability of the periodic radial vascularized tumor

**Setting.** In the planar free-boundary model of a vascularized tumor, with quasi-steady nutrient $\Delta u=u$, Robin vascular exchange $\partial_nu+\alpha(u-\phi(t))=0$, Darcy pressure $-\Delta p=\mu(u-\psi(t))$, curvature boundary condition $p=\kappa$ and normal velocity $V_n=-\partial_np$, let the supply $\phi$ and demand $\psi$ be positive $T$-periodic with $\bar\phi>\bar\psi$, so that a unique radially symmetric $T$-periodic solution $(u_\ast,p_\ast,R_\ast)$ exists. Perturb the boundary as $r=R_\ast(t)+\varepsilon\rho(\theta,t)$ and linearize.

**Theorem.** Assume the stronger pointwise condition $\phi_\ast=\min_t\phi(t)>\psi^\ast=\max_t\psi(t)$. Then there is $\mu_\ast>0$ such that for every aggressiveness $0<\mu<\mu_\ast$ the periodic radial solution is linearly stable: there are constants $a_1,b_1$ and $C,\delta>0$ with

$$\big|\rho(\theta,t)-\big(a_1\cos\theta+b_1\sin\theta\big)\big|\le Ce^{-\delta t}\qquad(t\to\infty).$$

The mode $n=1$ is not damped because it is a translation of the tumor center.

Under only the averaged condition $\bar\phi>\bar\psi$ the periodic solution exists, but no $\mu$-independent positive lower bound on $R_\ast$ is available, and linear stability is open.

## Expansion

Expanding $\rho$ in angular Fourier modes $\cos n\theta,\sin n\theta$ decouples the linearized problem into scalar periodic ODEs $\rho_n'=-A_n(t,\mu)\rho_n$, with coefficients built from ratios of modified Bessel functions $I_n$ evaluated at $R_\ast(t)$; $\rho_n$ decays exponentially iff $\int_0^TA_n\,dt>0$. The condition $\phi_\ast>\psi^\ast$ bounds $R_\ast(t;\mu)$ above and below uniformly in $\mu$, which keeps these Bessel ratios in a compact range. Since $\int_0^TR_\ast'/R_\ast\,dt=0$, the sign of $\int_0^TA_0$ reduces to a Bessel-ratio inequality and the radial mode $n=0$ decays for every $\mu>0$. For $n\ge 2$ the curvature term dominates once $\mu$ is small, and Bessel-function inequalities make the decay rate uniform in $n$, so every mode except the translational $n=1$ mode decays exponentially.

## Depends on

- [Averaged supply–demand dichotomy for a periodically fed vascularized tumor](averaged-supply-demand-dichotomy-for-a-periodically-fed-vascularized-tumor.md)

## Sources

- Xinyue Zhao, "A free-boundary model of vascularized tumor growth with time-periodic coefficients", arXiv:2606.11501 (2026), Theorem 1.2 and Section 3 (Lemmas 3.1, 3.2 and 3.4), with Lemmas B.1–B.2 on Bessel-function inequalities, <https://doi.org/10.48550/arXiv.2606.11501>.
