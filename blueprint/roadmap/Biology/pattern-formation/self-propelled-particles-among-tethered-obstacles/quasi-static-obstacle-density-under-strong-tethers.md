# Quasi-static obstacle density under strong tethers

Obstacles are tethered by linear springs to anchor points $y$ distributed with density $\rho_A \equiv 1$. They are pushed by self-propelled particles (SPPs) through a smooth even interaction kernel $\phi$. The obstacle distribution $f(x, y, t)$ satisfies

$$
\partial_t f + \nabla_x \cdot (\tilde v f) = \frac{1}{\gamma}\, \nabla_x \cdot \big((x - y) f + \delta \nabla_x f\big),
\qquad
\tilde v = -\frac{1}{\eta} \nabla_x \bar\rho_g, \quad \bar\rho_g = \phi * \rho_g ,
$$

where $\gamma = \eta/\kappa$ is the ratio of friction to spring stiffness, $\delta$ is the scaled obstacle noise, and $\rho_g$ is the SPP density. Expand $f = f_0 + \gamma f_1 + \gamma^2 f_2 + O(\gamma^3)$, with $\int f\,dx = 1$ for each anchor.

**Theorem 2 and Lemma 2.** Write $M_\delta(z) = (2\pi\delta)^{-n/2} e^{-|z|^2/(2\delta)}$. Then $f_0 = M_\delta(x - y)$. Because $\tilde v = \nabla V$ with $V = -\bar\rho_g/\eta$,

$$
f_1(x, y) = \frac{1}{\delta} M_\delta(x - y)\big(V(x) - (M_\delta * V)(y)\big).
$$

Consequently the macroscopic obstacle density $\rho_f = \int f\,dy$ is

$$
\rho_f = 1 - \frac{\gamma}{\delta\eta}\big[\bar\rho_g - M_{2\delta} * \bar\rho_g\big] - \frac{\gamma^2}{\eta}\, \partial_t \Delta_x \bar\rho_g + \frac{\gamma^2}{\eta^2} N(\bar\rho_g) + O(\gamma^2 \delta) + O(\gamma^3),
$$

with $N(\rho) = \tfrac{1}{2}\big((\Delta\rho)^2 - H(\rho) : H(\rho)\big)$, where $H$ is the Hessian. In the noiseless limit $\delta \to 0$,

$$
\rho_f = 1 + \frac{\gamma}{\eta}\Delta_x \bar\rho_g - \frac{\gamma^2}{\eta}\partial_t \Delta_x \bar\rho_g + \frac{\gamma^2}{\eta^2} N(\bar\rho_g) + O(\gamma^3),
$$

which equals $\det J_Y - \tfrac{\gamma^2}{\eta}\partial_t \Delta_x \bar\rho_g + O(\gamma^3)$ for the displacement map $Y(x) = x + \tfrac{\gamma}{\eta}\nabla_x \bar\rho_g(x)$.

## Expansion

The right-hand operator is a Fokker–Planck operator, $\delta\,\nabla_x \cdot \big(M_\delta \nabla_x (f / M_\delta)\big)$. Its kernel is spanned by the Gaussian $M_\delta(x - y)$, and it is solvable for right-hand sides of zero mass (Fredholm alternative). Matching powers of $\gamma$ gives $A_y(f_1) = \nabla_x \cdot (\tilde v f_0)$ and $A_y(f_2) = \partial_t f_1 + \nabla_x \cdot (\tilde v f_1)$. In the variable $\sigma = (x - y)/\sqrt{\delta}$ these become Ornstein–Uhlenbeck equations with polynomial right-hand sides, solved with Hermite polynomials. For a conservative drift, the first-order solution is explicit, and integrating over anchors gives $\rho_{f,1} = -(\delta\eta)^{-1}[\bar\rho_g - M_{2\delta} * \bar\rho_g] = \eta^{-1}\Delta\bar\rho_g + O(\delta)$. Physically, obstacles are displaced down the gradient of SPP density. The $\partial_t$ term is a memory effect: obstacles respond to the SPP density at time $t - \gamma$.

## Sources

- Aceves-Sanchez P, Degond P, Keaveny EE, Manhart A, Merino-Aceituno S, Peurichard D. Large-scale dynamics of self-propelled particles moving through obstacles: model derivation and pattern formation. *Bulletin of Mathematical Biology* 82 (2020) 129. <https://doi.org/10.1007/s11538-020-00805-z>. PMCID: PMC7519010.
