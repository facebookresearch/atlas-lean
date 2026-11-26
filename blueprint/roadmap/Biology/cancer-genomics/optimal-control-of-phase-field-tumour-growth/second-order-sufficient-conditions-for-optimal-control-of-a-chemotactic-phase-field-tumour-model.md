# Second-order sufficient conditions for optimal control of a chemotactic phase-field tumour model

**Setting.** On a smooth bounded domain $\Omega \subset \mathbb R^3$ and time horizon $(0,T)$, with $Q = \Omega \times (0,T)$, the tumour fraction $\varphi \in [-1,1]$, chemical potential $\mu$ and nutrient $\sigma$ satisfy the viscous Cahn–Hilliard–reaction–diffusion system with chemotaxis

$$\alpha\partial_t\mu + \partial_t\varphi - \Delta\mu = P(\varphi)\big(\sigma + \chi(1-\varphi) - \mu\big) - \mathbb h(\varphi)u_1,$$

$$\beta\partial_t\varphi - \Delta\varphi + F'(\varphi) = \mu + \chi\sigma, \qquad \partial_t\sigma - \Delta\sigma = -\chi\Delta\varphi - P(\varphi)\big(\sigma + \chi(1-\varphi) - \mu\big) + u_2,$$

with homogeneous Neumann conditions and initial data, where $\alpha,\beta > 0$, $P$ is a proliferation function, $\chi > 0$ the chemotactic sensitivity, $F$ a double-well potential (possibly singular, e.g. logarithmic), $u_1$ a cytotoxic drug acting through $\mathbb h(\varphi)$ and $u_2$ a nutrient supply. The **control problem** is to minimize

$$\mathcal J = \frac{b_1}{2}\int_Q |\varphi - \hat\varphi_Q|^2 + \frac{b_2}{2}\int_\Omega |\varphi(T) - \hat\varphi_\Omega|^2 + \frac{b_0}{2}\int_Q |\mathbf u|^2$$

over a nonempty closed convex set $\mathcal U_{ad} \subset L^\infty(Q)^2$ of admissible controls, with $b_1, b_2 \ge 0$ and $b_0 > 0$.

**Theorem.** Under the paper's assumptions on $F$, $P$, $\mathbb h$, the data and $\mathcal U_{ad}$ (including strict separation of $\varphi_0$ from the singularities of $F$):
1. (Theorems 2.2 and 3.1) The state system is well posed, the control-to-state map $\mathcal S$ is defined on a neighbourhood of $\mathcal U_{ad}$, and the problem admits a minimizer.
2. (Theorems 4.1–4.4) $\mathcal S$ is twice continuously Fréchet differentiable; the first and second derivatives are the unique solutions of the linearized and bilinearized systems, and both are Lipschitz continuous in the control.
3. (Theorems 5.1–5.3) If $\bar{\mathbf u}$ is optimal with state $(\bar\mu,\bar\varphi,\bar\sigma)$ and adjoint state $(p,q,r)$, then with $\mathbf d = (-\mathbb h(\bar\varphi)p,\ r)$,

$$\int_Q (\mathbf d + b_0\bar{\mathbf u})\cdot(\mathbf u - \bar{\mathbf u}) \ge 0 \quad \forall\,\mathbf u \in \mathcal U_{ad},$$

so $\bar{\mathbf u}$ is the $L^2(Q)^2$-orthogonal projection of $-b_0^{-1}\mathbf d$ onto $\mathcal U_{ad}$.
4. (Theorem 6.1) If an admissible $\bar{\mathbf u}$ satisfies the first-order condition and the second derivative of the reduced cost is coercive on the relevant critical directions (condition (C4)), then there are $\varepsilon_1,\varepsilon_2 > 0$ with $\mathcal J_{red}(\mathbf u) \ge \mathcal J_{red}(\bar{\mathbf u}) + \varepsilon_1\lVert\mathbf u - \bar{\mathbf u}\rVert^2_{L^2(Q)^2}$ whenever $\lVert\mathbf u - \bar{\mathbf u}\rVert_{L^\infty(Q)^2} \le \varepsilon_2$; in particular $\bar{\mathbf u}$ is locally optimal.

## Expansion

The viscosity terms $\alpha\partial_t\mu$ and $\beta\partial_t\varphi$ give enough parabolic regularity that $\varphi$ stays uniformly away from $\pm1$ even for singular potentials, so $F'$, $F''$ and $F^{(3)}$ are bounded along solutions; this separation property is what makes the control-to-state map twice differentiable. The first-order condition follows from the variational inequality for the reduced cost by introducing the adjoint system, which removes the linearized state. Because the control space $L^\infty$ differs from the space $L^2$ in which the quadratic growth holds (the two-norm discrepancy), the second-order argument combines Lipschitz bounds on $D\mathcal S$ and $D^2\mathcal S$ with a Taylor expansion of the reduced cost. Second-order sufficient conditions are the standard prerequisite for stability of optimal treatment schedules and convergence of numerical optimization.

## Sources

- Pierluigi Colli, Andrea Signori and Jürgen Sprekels, "Second-order analysis of an optimal control problem in a phase field tumor growth model with singular potentials and chemotaxis", arXiv:2009.07574 (2020), Section 1 (problem (CP) and state system), Theorems 2.2, 3.1, 4.1–4.4, 5.1–5.3 and 6.1, <https://doi.org/10.48550/arXiv.2009.07574>. Published version: ESAIM Control Optim. Calc. Var. 27 (2021), paper No. 73, pp. 1-46, <https://doi.org/10.1051/cocv/2021072>.
