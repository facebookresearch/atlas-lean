# Unique determination of attraction–repulsion chemotaxis coefficients from boundary data

**System.** On a bounded domain $\Omega\subset\mathbb R^n$ with $Q=\Omega\times(0,T)$ and $\Sigma=\partial\Omega\times(0,T)$, a cell density $u$ moves up the gradient of an attractant $v$ and down the gradient of a repellent $w$:

$$
\begin{cases}
\partial_tu=\Delta u-\nabla\cdot(\chi u\nabla v)+\nabla\cdot(\xi u\nabla w)+F(x,u) & \text{in } Q,\\
\tau\,\partial_tv=\Delta v+G(x,u,v) & \text{in } Q,\\
\tau\,\partial_tw=\Delta w+H(x,u,w) & \text{in } Q,\\
\partial_\nu u=\partial_\nu v=\partial_\nu w=0 & \text{on } \Sigma,\\
u(\cdot,0)=f,\ v(\cdot,0)=g,\ w(\cdot,0)=h & \text{in } \Omega,
\end{cases}
$$

with $\tau\in\{0,1\}$ ($\tau=0$: parabolic–elliptic–elliptic; $\tau=1$: fully parabolic), chemotactic sensitivities $\chi,\xi$ and analytic reaction terms, for example logistic growth $F=ru-\mu u^2$. The **measurement map** sends initial data to the boundary traces and final-time states of nonnegative solutions,

$$
\mathcal M^+_{\chi,\xi,F,G,H}(f,g,h)=\bigl(u|_\Sigma,\ v|_\Sigma,\ w|_\Sigma,\ u(\cdot,T),\ v(\cdot,T),\ w(\cdot,T)\bigr).
$$

**Theorem (Theorem 1.5).** Let $(u_0,v_0,w_0)$ be a known nonnegative constant steady state. Suppose $F,G,H$ are admissible in the sense of the source's Definitions 1.1, 1.3 and 1.4 ($F\in\mathcal A$, $G\in\mathcal B$, $H\in\mathcal C$): each is holomorphic in the state variables with values in $C^{2+\alpha}_0(\overline\Omega)$ and vanishes at the steady state; for $G$ and $H$ the first-order Taylor coefficient in the signal variable ($G^{(0,1)}$, $H^{(0,1)}$) is constant, the first-order coefficient in $u$ ($G^{(1,0)}$, $H^{(1,0)}$) is independent of one spatial variable, and every Taylor coefficient of order $k\ge2$ is of multiplicative separable form, $A(x)=A_1(x_1,\dots,x_{n-1})A_2(x_n)$ with $\int_{\{x_n:(x_1,\dots,x_n)\in\Omega\}}A_2(x_n)\,dx_n\ne0$ (Definition 1.2); suppose $\chi,\xi$ and all orders of the high-order variations of $(u,v,w)$ are independent of one spatial variable, and that solutions exist in $C^{1+\alpha/2,2+\alpha}$. If two parameter sets $A_j=(\chi_j,\xi_j,F_j,G_j,H_j)$, $j=1,2$, satisfy $\mathcal M^+_{A_1}(f,g,h)=\mathcal M^+_{A_2}(f,g,h)$ for all $(f,g,h)\in C^{2+\alpha}(\Omega)^3$, then $A_1=A_2$.

**Corollary (Corollary 1.6).** For the attraction–repulsion model with logistic growth and linear signal kinetics,

$$
\partial_tu=\Delta u-\nabla\cdot(\chi u\nabla v)+\nabla\cdot(\xi u\nabla w)+ru-\mu u^2,\quad \tau\partial_tv=\Delta v+\alpha u-\beta v,\quad \tau\partial_tw=\Delta w+\gamma u-\delta w,
$$

with zero-flux boundary conditions, and given $\beta,\delta,\chi,\xi$ satisfying the theorem's hypotheses, equal measurement maps for all initial data force equality of $(\chi,\xi,r,\mu,\alpha,\beta,\gamma,\delta)$.

## Expansion

Take initial data $(u_0,v_0,w_0)+\sum_k\varepsilon^k(f_k,g_k,h_k)/k!$ and differentiate the solution in $\varepsilon$ at $0$ (high-order variation). The first-order variation solves a linear system with constant coefficients around the constant state; its boundary and final-time data determine the linear Taylor coefficients of $F,G,H$ and the products $\chi u_0$, $\xi u_0$, using special exponential solutions $e^{\theta t}l(x;\theta)$ of $\partial_tu-q\Delta u+ku=0$ with Neumann data and the multiplicative-separable structure (independence of one variable) to pass from integral identities to pointwise equality. Each higher-order variation solves the same linear operator with a source built from lower orders and the next Taylor coefficient, so induction recovers every coefficient. Positivity is preserved because the perturbations are around a nonnegative constant state.

## Sources

- Y. Li, H. Liu and C. W. K. Lo, "Determining a parabolic-elliptic-elliptic system by boundary observation of its non-negative solutions with biological applications", arXiv:2509.04850 (2025), Section 1.2 (setup, measurement map, Definitions 1.1–1.4), Section 1.3 (Theorem 1.5, Corollary 1.6) and Section 2 (proof by high-order variation), <https://doi.org/10.48550/arXiv.2509.04850>.
