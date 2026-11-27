# Global boundedness and small-coupling uniqueness for look-ahead pheromone chemotaxis of active Brownian ants

**Model.** Ants are active Brownian particles on the flat torus $\mathbb{T}^2$ with orientation $\theta \in \mathbb{T}_{2\pi}$, heading $\mathbf{e}_\theta = (\cos\theta, \sin\theta)$ and normal $\mathbf{n}_\theta = (-\sin\theta, \cos\theta)$. Each ant turns its heading up the gradient of a pheromone field sensed at a look-ahead distance $\lambda \ge 0$ in front of it. In rescaled form, the mean-field density $f(t, \mathbf{x}, \theta)$ (a probability density) and the quasi-stationary pheromone concentration $c(t, \mathbf{x})$ satisfy

$$\partial_t f = \nabla_{\mathbf{x}}\cdot\big[D_T\nabla_{\mathbf{x}} f - \mathrm{Pe}\,\mathbf{e}_\theta f\big] + \partial_\theta\big[\partial_\theta f - \gamma\,(\mathbf{n}_\theta\cdot\nabla_{\mathbf{x}} c_\lambda)\,f\big],$$

$$0 = \Delta_{\mathbf{x}} c - \alpha c + \rho, \qquad \rho(t,\mathbf{x}) = \int_0^{2\pi} f\,d\theta, \qquad c_\lambda(t,\mathbf{x},\theta) = c(t, \mathbf{x} + \lambda\mathbf{e}_\theta),$$

with translational diffusion $D_T > 0$, Péclet number (self-propulsion) $\mathrm{Pe}$, alignment strength $\gamma \ge 0$ and pheromone decay $\alpha > 0$. The spatial density obeys $\partial_t\rho = \nabla\cdot[D_T\nabla\rho - \mathrm{Pe}\,\mathbf{p}]$ with polarization $\mathbf{p} = \int \mathbf{e}_\theta f\,d\theta$, so chemotaxis enters only through the orientation dynamics, unlike Keller–Segel.

**Theorem.**
1. *Existence.* For every $T > 0$ and nonnegative $f_{\mathrm{in}} \in L^2$ there is a nonnegative weak solution $f \in L^2(0,T; H^1) \cap C(0,T; L^2)$ with $\partial_t f \in L^2(0,T; (H^1)')$.
2. *No blow-up.* If moreover $f_{\mathrm{in}} \in L^2 \cap L^\infty$, the solution extends to all times and $\sup_{t\ge0}\|f(t)\|_{L^\infty} \le C_\infty$, with $C_\infty$ depending only on $D_T, \mathrm{Pe}, \gamma, \lambda, \alpha$ and $\|f_{\mathrm{in}}\|_{L^\infty}$.
3. *Uniqueness of the stationary state for weak coupling.* For fixed $D_T, \mathrm{Pe}, \lambda, \alpha$ and $\gamma$ small enough, every nonnegative weak stationary solution equals the homogeneous state $f_* = \frac{1}{2\pi}$.
4. *Nonlinear stability.* If the linearized operator at $f_*$ satisfies an exponential decay estimate with rate $\beta > 0$ and $\gamma < 2f_*\min\{D_T, 1\}/\alpha$, then sufficiently small perturbations in $H^2_{\mathbf{x}}L^2_\theta$ decay at any exponential rate $\delta_0 < \beta$.

## Proof sketch

Because $|\mathbf{p}| \le \rho$, multiplying the $\rho$-equation by $\rho^p$ and using Young's and the two-dimensional Gagliardo–Nirenberg inequality gives $L^{p+1}$ bounds that do not depend on the chemotactic term; Alikakos' $L^p$ iteration then yields a uniform $L^\infty$ bound on $\rho$, elliptic regularity bounds $\nabla c$, and a second iteration bounds $f$. So, in contrast with Keller–Segel, orientation-mediated chemotaxis cannot concentrate mass into a singularity. For small $\gamma$, an $L^2$ energy estimate on the difference of two stationary solutions forces them to coincide. Patterns therefore require $\gamma$ beyond a threshold; numerically, the look-ahead distance $\lambda$ selects between aggregation spots and lane formation.

## Sources

- Maria Bruna, Martin Burger and Oscar de Wit, "Lane Formation and Aggregation Spots in a Model of Ants", *SIAM Journal on Applied Dynamical Systems* 24 (2025), 675–709, <https://doi.org/10.1137/24m1634527>. Preprint version: arXiv:2401.15046 (2024), macroscopic model (Section 2.2), and in Section 3 the existence theorem with its weak-solution definition, the no-blow-up proposition (Section 3.1), the conditional uniqueness proposition (Section 3.2) and the conditional nonlinear stability proposition (Section 3.3), <https://doi.org/10.48550/arXiv.2401.15046>.
