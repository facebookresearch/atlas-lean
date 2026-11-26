# Global attractivity of the endemic state of a nonlocal delayed diffusive dengue model for $\Re_0>1$

**Model.** On a bounded domain $\Omega\subset\mathbb R^n$ with Neumann boundary conditions let $u_1$ be the density of infectious mosquitoes, $u_2$ of susceptible humans and $u_3$ of infectious humans. With incubation delays $\tau_a$ (in mosquitoes) and $\tau_b$ (in humans), diffusion rates $d_m,d_h$, and $\Gamma(t,x,y)$ the Neumann heat kernel on $\Omega$ (which transports individuals that move during the incubation period),

$$\partial_tu_1=d_m\Delta u_1+\beta_m(A-u_1)\int_\Omega\Gamma(d_m\tau_a,x,y)\,u_3(t-\tau_a,y)\,dy-\mu_mu_1,$$

$$\partial_tu_2=d_h\Delta u_2+H-\beta_hu_1u_2-\mu_hu_2,$$

$$\partial_tu_3=d_h\Delta u_3+\beta_he^{-\mu_h\tau_b}\int_\Omega\Gamma(d_h\tau_b,x,y)\,u_1(t-\tau_b,y)\,u_2(t-\tau_b,y)\,dy-\rho_hu_3,$$

where $A$ is the total mosquito density, $H$ the human recruitment rate, $\beta_m=bp$ and $\beta_h=bq$ the transmission rates (biting rate times infection probabilities), $\mu_m,\mu_h$ death rates and $\rho_h=\mu_h+\gamma_h$ with recovery rate $\gamma_h$. The basic reproduction number is

$$\Re_0=\sqrt{\frac{\beta_h\beta_mAH\,e^{-\mu_h\tau_b}}{\mu_h\mu_m\rho_h}}.$$

**Theorem.** If $\Re_0>1$, the system has a unique positive constant steady state $u^\ast=(u_1^\ast,u_2^\ast,u_3^\ast)$, and every solution with non-negative initial history in the invariant region and with $\phi_1(0,\cdot)\not\equiv0$ or $\phi_3(0,\cdot)\not\equiv0$ satisfies $u(t,x)\to u^\ast$ as $t\to\infty$, uniformly for $x\in\overline\Omega$.

This removes the extra sufficient condition $\Re_0>\max\{1,\sqrt{A\beta_h/\mu_h}\}$ under which the same convergence had previously been obtained by the fluctuation method, so convergence to the endemic state holds on the whole range $\Re_0>1$.

## Depends on

- [Next-generation matrix and the basic reproduction number](../next-generation-matrix-and-the-basic-reproductio/README.md)

## Expansion

With $g(\omega)=\omega-1-\ln\omega\ge0$ (zero only at $\omega=1$), use the Volterra-type Lyapunov functional $V(t)=\int_\Omega\bigl(L_1+L_2+L_3+W_1+W_2\bigr)\,dx$ where

$$L_1=\frac{\beta_hu_1^\ast u_2^\ast}{\mu_m}\,g\Bigl(\frac{u_1}{u_1^\ast}\Bigr),\qquad L_2=u_2^\ast\,g\Bigl(\frac{u_2}{u_2^\ast}\Bigr),\qquad L_3=e^{\mu_h\tau_b}u_3^\ast\,g\Bigl(\frac{u_3}{u_3^\ast}\Bigr),$$

and $W_1$, $W_2$ integrate $g(u_3(t+\theta,y)/u_3^\ast)$ over $\theta\in[-\tau_a,0]$ and $g(u_1u_2(t+\theta,y)/(u_1^\ast u_2^\ast))$ over $\theta\in[-\tau_b,0]$ against the kernels $\Gamma(d_m(-\theta),x,y)$ and $\Gamma(d_h(-\theta),x,y)$, both weighted by $\beta_hu_1^\ast u_2^\ast$. The diffusion terms contribute non-positive gradient integrals (by the divergence theorem with Neumann conditions and convexity of $-\ln$), the delay terms telescope against $W_1,W_2$ thanks to the semigroup property and symmetry of $\Gamma$, and the remaining reaction terms combine, using the equilibrium relations, into $-\int g(\cdot)$ terms and arithmetic–geometric-mean inequalities. Thus $V$ is non-increasing, and LaSalle's invariance principle on the compact attractor shows that the largest invariant set where $\dot V=0$ is $\{u^\ast\}$.

## Sources

- Xue Ren, Ran Zhang, "Global Attractivity of a Nonlocal Delayed Diffusive Dengue Model in a Spatially Homogeneous Environment", arXiv (2026). Section 1 (model and Theorem 1.1, recalling the earlier sufficient condition), Section 2 (Theorem 2.1 and its Lyapunov-functional proof). <https://doi.org/10.48550/arXiv.2602.00714>
