# Reaction–diffusion on an anisotropically growing manifold pulled back to a fixed domain

Let $\Omega(t) \subset \mathbb R^3$, $t \ge 0$, be a smooth compact two-dimensional manifold (with or without boundary) parametrized by

$$X(\alpha, \beta, t), \qquad (\alpha, \beta) \in \Phi = [\alpha_1, \alpha_2] \times [\beta_1, \beta_2],$$

with $\partial_\alpha X \times \partial_\beta X \ne 0$ off a null set. Let $G = (g_{ij})$ be the metric tensor, $g_{11} = |\partial_\alpha X|^2$, $g_{12} = g_{21} = \partial_\alpha X \cdot \partial_\beta X$, $g_{22} = |\partial_\beta X|^2$, with inverse entries $G^{-1}_{ij}$; the parametrization need not be orthogonal ($g_{12} \ne 0$ is allowed), which is what permits anisotropic growth. Morphogens $u, v$ on $\Omega(t)$ obey conservation of mass with Fickian flux and kinetics $f, g$, so by Reynolds' transport theorem

$$\partial_t u + \nabla_{\Omega(t)} \cdot (Q u) = \delta_1 \nabla^2_{\Omega(t)} u + f(u, v), \qquad \partial_t v + \nabla_{\Omega(t)} \cdot (Q v) = \delta_2 \nabla^2_{\Omega(t)} v + g(u, v),$$

where $Q$ is the velocity field of the growing surface and $\nabla^2_{\Omega(t)}$ the Laplace–Beltrami operator.

**Pulled-back system.** Assume space and time separate in $X$ (dilational growth). In the material coordinates $(\alpha, \beta)$ the advection term $Q \cdot \nabla u$ is absorbed, the divergence of the growth field is

$$\nabla_{\Omega(t)} \cdot Q = \partial_t \log \sqrt{|\det G|},$$

and the system becomes the spatially and temporally heterogeneous reaction–diffusion system on the fixed domain $\Phi$

$$\partial_t u = \frac{\delta_1}{\sqrt{|\det G|}} \sum_{i,j \in \{\alpha, \beta\}} \partial_i\!\left(\sqrt{|\det G|}\; G^{-1}_{ij}\, \partial_j u\right) - \big(\partial_t \log \sqrt{|\det G|}\big)\, u + f(u, v),$$

and likewise for $v$ with $\delta_2$ and $g$. The middle term is dilution by local area change.

**Growing ellipse.** For the planar ellipse $X = (A(t)\, \alpha \cos\beta,\ B(t)\, \alpha \sin\beta,\ 0)$, $\alpha \in [0,1]$, one finds $\det G = A^2 B^2 \alpha^2$ and a dilution rate $\dot A / A + \dot B / B$. In Cartesian material coordinates $(\xi, \eta) = (x/A, y/B)$ on the unit disk the same pull-back reads

$$\partial_t u = \delta_1\left(\frac{1}{A(t)^2}\, \partial_\xi^2 u + \frac{1}{B(t)^2}\, \partial_\eta^2 u\right) - \left(\frac{\dot A}{A} + \frac{\dot B}{B}\right) u + f(u, v),$$

so anisotropic growth acts as direction-dependent, time-dependent effective diffusion. When $A \equiv B$ (an isotropically growing disk) it reduces to $\partial_t u = (\delta_1 / A^2)\, \Delta u - 2 (\dot A / A)\, u + f(u, v)$ in polar material coordinates.

## Depends on

- [Diffusion-driven instability (Turing 1952)](turing-instability.md)

## Expansion

Reynolds' transport theorem gives $\frac{d}{dt}\int_{\hat\Omega(t)} u\, d\Omega = \int_{\hat\Omega(t)} \big(\partial_t u + \nabla \cdot (Q u)\big)\, d\Omega$ for every material area element $\hat\Omega(t)$, and Fick's law turns the flux into $-\delta \nabla u$. Writing $\nabla \cdot (Qu) = (\nabla \cdot Q)\, u + Q \cdot \nabla u$, the time derivative at fixed material coordinates contributes exactly $-Q \cdot \nabla u$, cancelling advection. The area element is $\sqrt{|\det G|}\, d\alpha\, d\beta$, so the relative rate of change of local area, which is $\nabla \cdot Q$, is $\partial_t \log \sqrt{|\det G|}$; with a diagonal metric this reduces to $\partial_t \log(|\partial_\alpha X|\, |\partial_\beta X|)$, the form used by Plaza et al. (2004) for orthogonal growth. The Laplace–Beltrami operator in local coordinates is the standard divergence form above. For the ellipse the map $(\xi, \eta) \mapsto (A\xi, B\eta)$ is linear, so the Laplacian pulls back to $A^{-2}\partial_\xi^2 + B^{-2}\partial_\eta^2$, and the area factor $AB$ gives the dilution rate. Krause, Ellis and Van Gorder also treat a growing triaxial ellipsoid surface this way and use simulations with Schnakenberg, Gierer–Meinhardt and FitzHugh–Nagumo kinetics to compare isotropic, staged anisotropic and fast growth.

## Sources

- A. L. Krause, M. A. Ellis and R. A. Van Gorder, "Influence of curvature, growth, and anisotropy on the evolution of Turing patterns on growing manifolds", Bulletin of Mathematical Biology (2018), Section 2 (Equations 4–17 for the general pull-back, Equations 19–26 for the ellipse), <https://doi.org/10.1007/s11538-018-0535-y> (PMC6373535).
