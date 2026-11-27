# Optimal nutrient supply in a viscous Cahn–Hilliard–Keller–Segel tumour model

**State system.** On a smooth bounded $\Omega\subset\mathbb R^3$, $Q=\Omega\times(0,T)$, the tumour phase field $\phi\in(-1,1)$, chemical potential $\mu$ and nutrient $\sigma\ge0$ satisfy, with homogeneous Neumann conditions,

$$\begin{aligned} \partial_t\phi-\Delta\mu+m\phi&=\gamma(\phi,\sigma),\\ \tau\partial_t\phi-\Delta\phi+F'(\phi)-\sigma&=\mu,\\ \partial_t\sigma-\Delta\sigma+\nabla\cdot(\sigma\nabla\phi)&=\sigma-\sigma^2+u, \end{aligned}$$

where $\tau,m>0$, the source $\gamma\in C^2$ is bounded with bounded derivatives and $\sup|\gamma|<m$, and $F$ is the logarithmic double well

$$F(s)=(1+s)\ln(1+s)+(1-s)\ln(1-s)-c_0s^2\quad(|s|\le1),\qquad c_0>1 .$$

The nutrient equation couples logistic nutrient dynamics with a Keller–Segel cross-diffusion term driven by the phase field; the distributed control $u$ is a nutrient supply.

**Theorem (well-posedness, separation, stability).** For smooth initial data with $\|\phi_0\|_\infty<1$, $\sigma_0\ge0$ bounded, and $u\in L^\infty(Q)$ with $\|u\|_\infty\le M$, there is a unique solution with $\phi\in W^{1,\infty}(0,T;H^1)\cap H^1(0,T;H^2)\cap L^\infty(0,T;H^3)$, $\mu\in L^\infty(0,T;H^2)$, $\sigma\in H^1(0,T;L^2)\cap C^0([0,T];H^1)\cap L^2(0,T;H^2)\cap L^\infty(Q)$, $\sigma\ge0$, satisfying bounds independent of $u$ and the **separation property**

$$|\phi|\le1-\delta_0\quad\text{a.e. in }Q$$

for some $\delta_0\in(0,1)$ depending only on the data and $M$. Solutions depend Lipschitz-continuously on the control: $\|\phi_1-\phi_2\|+\|\mu_1-\mu_2\|+\|\sigma_1-\sigma_2\|\le K_2\|u_1-u_2\|_{L^2(Q)}$ in the natural norms.

**Control problem.** Minimize

$$\mathcal J=\frac{\alpha_1}2\int_Q|\phi-\phi_Q|^2+\frac{\alpha_2}2\int_\Omega|\phi(T)-\phi_\Omega|^2+\frac{\alpha_3}2\int_Q|\sigma-\sigma_Q|^2+\frac{\alpha_4}2\int_\Omega|\sigma(T)-\sigma_\Omega|^2+\frac{\alpha_5}2\int_Q|u|^2$$

over $\mathcal U_{ad}=\{u\in L^\infty(Q):u_{\min}\le u\le u_{\max}\}$, $\alpha_i\ge0$.

**Theorem (existence and first-order conditions).** An optimal control $u^*$ exists. The control-to-state map is Fréchet differentiable (its derivative solves the linearized system), the adjoint system has a unique solution $(p,q,r)$, and

$$\int_Q\big(r+\alpha_5u^*\big)(u-u^*)\ge0\qquad\forall\,u\in\mathcal U_{ad};$$

if $\alpha_5>0$, $u^*$ is the $L^2(Q)$ projection of $-r/\alpha_5$ onto $\mathcal U_{ad}$, i.e. $u^*=\max\{u_{\min},\min\{u_{\max},-r/\alpha_5\}\}$.

## Expansion

The viscous term $\tau\partial_t\phi$ and the mass term $m\phi$ with $\sup|\gamma|<m$ give uniform $L^\infty$ bounds on $\mu$; combined with the logarithmic singularity this keeps $\phi$ strictly inside $(-1,1)$, so $F'(\phi)$ and its derivatives are bounded along solutions. That makes the cross-diffusion term $\nabla\cdot(\sigma\nabla\phi)$ manageable: $\nabla\phi$ is bounded in $L^\infty(0,T;H^2)$, and a maximum-principle argument keeps $\sigma$ nonnegative and bounded. Existence of an optimal control is the direct method with weak-star compactness of $\mathcal U_{ad}$; the adjoint system is solved after the change of unknowns $z=p+\tau q$, and the variational inequality follows from the chain rule for the reduced cost.

## Sources

- Gianni Gilardi, Andrea Signori, Jürgen Sprekels, "Nutrient control for a viscous Cahn–Hilliard–Keller–Segel model with logistic source describing tumor growth", Discrete and Continuous Dynamical Systems - S 16 (2023), 3552–3572, <https://doi.org/10.3934/dcdss.2023123>. Published version of arXiv:2309.09052, cited next; locators there refer to the arXiv version.
- Gianni Gilardi, Andrea Signori, Jürgen Sprekels, "Nutrient control for a viscous Cahn–Hilliard–Keller–Segel model with logistic source describing tumor growth", arXiv:2309.09052 (2023): structural assumptions and Theorems on well-posedness and continuous dependence (Section 2), existence of an optimal control, Fréchet differentiability, adjoint well-posedness and the first-order optimality condition (Section 4). <https://doi.org/10.48550/arXiv.2309.09052>
