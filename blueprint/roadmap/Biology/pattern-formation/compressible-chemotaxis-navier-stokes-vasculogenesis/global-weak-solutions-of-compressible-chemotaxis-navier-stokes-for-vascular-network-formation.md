# Global weak solutions of compressible chemotaxis Navier–Stokes for vascular network formation

**Model.** On the three-dimensional torus $\Omega = \mathbb{T}^3$, let $\rho(x,t) \ge 0$ be the density of endothelial cells, $v(x,t)$ their velocity and $c(x,t)$ the chemoattractant concentration, satisfying

$$\partial_t \rho + \operatorname{div}(\rho v) = 0,$$

$$\partial_t(\rho v) + \operatorname{div}(\rho v \otimes v) + \nabla p(\rho) = \nu \operatorname{div}\big(\rho \, \mathbb{D}(v)\big) + \rho \nabla c - \frac{\rho v}{\zeta},$$

$$\partial_t c = \Delta c - c + \rho,$$

with $\mathbb{D}(v) = \tfrac12(\nabla v + \nabla v^T)$, pressure $p(\rho) = \rho^\gamma$ with adiabatic exponent $\gamma > 1$, density-dependent viscosity coefficient $\nu \rho$ ($\nu > 0$), and drag relaxation time $\zeta > 0$. The chemotactic force $\rho \nabla c$ enters the momentum balance, and cells produce the signal they respond to. Initial data satisfy $\rho^0 \in L^\gamma(\Omega)$, $\sqrt{\rho^0} \in H^1(\Omega)$, $c^0 \in H^1(\Omega)$ and $\sqrt{\rho^0} v^0 \in L^2(\Omega; \mathbb{R}^3)$.

**Theorem.** Let $T > 0$ and $\gamma > 4/3$. Then the system has a global weak solution $(\sqrt\rho, \sqrt\rho v, c)$ on $[0,T]$: the continuity and chemoattractant equations hold in the distributional sense, and the momentum equation holds in the weak form

$$\int_0^T\!\!\int_\Omega \big(\rho v \cdot \partial_t\psi + (\rho v \otimes v) : \nabla\psi - \nabla p(\rho)\cdot\psi + \rho \nabla c \cdot \psi\big)\,dx\,dt = \int_0^T\!\!\int_\Omega \Big(\frac{\rho v}{\zeta}\cdot\psi + \sqrt{\nu\rho}\,\mathbb{S}_\nu : \nabla\psi\Big)\,dx\,dt$$

for all test fields $\psi \in C_0^\infty(\Omega \times (0,T); \mathbb{R}^3)$, where $\mathbb{S}_\nu = \tfrac12(\mathbb{T}_\nu + \mathbb{T}_\nu^T)$ and the tensor $\mathbb{T}_\nu \in L^2$ is defined by $\sqrt{\nu\rho}\,\mathbb{T}_\nu = \nu\nabla(\rho v) - 2\nu\sqrt\rho\, v \otimes \nabla\sqrt\rho$ (it equals $\sqrt{\nu\rho}\,\nabla v$ for smooth positive $\rho$; the weak form avoids $1/\sqrt\rho$ and $\nabla v$, which need not exist).

The threshold $\gamma > 4/3$ coincides with the exponent known for existence in degenerate Keller–Segel equations with pressure $\rho^\gamma$.

## Expansion

The proof regularizes with a Korteweg capillarity term $\kappa \rho \nabla(\Delta\sqrt\rho/\sqrt\rho)$ and drag terms $r_0 v + r_1 \rho |v|^2 v$, for which global weak solutions exist for every $\gamma > 1$. The key uniform bounds come from the energy inequality together with the Bresch–Desjardins (BD) entropy inequality, which controls $\nabla\sqrt\rho$ and $\nabla \rho^{\gamma/2}$. The chemotactic energy term $\int \rho c$ has no sign; it is absorbed by $\sigma_1 \int \rho^\gamma + \sigma_2 \int |\nabla c|^2$ when $\gamma > 8/5$, and by $\int |\nabla \sqrt\rho|^2$ from the BD entropy otherwise. For $\gamma > 4/3$ these bounds are independent of the regularization parameters, and the limit $(\kappa, r_0, r_1) \to 0$ is passed through solutions renormalized in the velocity variable.

## Sources

- A. Jüngel and F. Philipp, "Chemotaxis compressible Navier–Stokes equations with density-dependent viscosity modeling vascular network formation", arXiv:2604.24725 (2026), Section 1 (model and Definitions 1–2), Theorem 1, Theorem 2, Lemma 3 and Lemma 7 (BD entropy inequality), <https://doi.org/10.48550/arXiv.2604.24725>.
