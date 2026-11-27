# Reaction–diffusion on an anisotropically growing manifold pulled back to a fixed domain

Let $\Omega(t) \subset \mathbb R^3$, $t \ge 0$, be a smooth compact two-dimensional manifold (with or without boundary) parametrized by

$$X(\alpha, \beta, t), \qquad (\alpha, \beta) \in \Phi = [\alpha_1, \alpha_2] \times [\beta_1, \beta_2],$$

with $\partial_\alpha X \times \partial_\beta X \ne 0$ off a null set. Let $G = (g_{ij})$ be the metric tensor, $g_{11} = |\partial_\alpha X|^2$, $g_{12} = g_{21} = \partial_\alpha X \cdot \partial_\beta X$, $g_{22} = |\partial_\beta X|^2$, with inverse entries $G^{-1}_{ij}$. The parametrization need not be orthogonal ($g_{12} \ne 0$ is allowed). Anisotropic growth means unequal stretching in different directions; it does not require a nonorthogonal parametrization, as the ellipse below has a diagonal metric in Cartesian material coordinates. Let $Q = \partial_t X$ be the velocity field of the growing surface, viewed as a field on $\Omega(t)$. Morphogens $u, v$ on $\Omega(t)$ obey conservation of mass with Fickian flux and kinetics $f, g$, so by Reynolds' transport theorem

$$\partial_t u + \nabla_{\Omega(t)} \cdot (Q u) = \delta_1 \nabla^2_{\Omega(t)} u + f(u, v), \qquad \partial_t v + \nabla_{\Omega(t)} \cdot (Q v) = \delta_2 \nabla^2_{\Omega(t)} v + g(u, v),$$

where $\nabla^2_{\Omega(t)}$ is the [Laplace–Beltrami operator](../../../Geometry/riemannian-geometry/laplace-beltrami-operator/laplacian.md) of $\Omega(t)$. Where $\Omega(t)$ has a boundary, both species satisfy zero conormal flux,

$$\mathbf n_\partial \cdot \nabla_{\Omega(t)} u = 0, \qquad \mathbf n_\partial \cdot \nabla_{\Omega(t)} v = 0 \qquad \text{on } \partial\Omega(t),$$

where $\mathbf n_\partial$ is the outward unit conormal, the unit vector tangent to $\Omega(t)$ and normal to $\partial\Omega(t)$.

**Pulled-back system.** Assume space and time separate in $X$ (dilational growth). Let $U(\alpha, \beta, t) = u(X(\alpha, \beta, t), t)$ and $V(\alpha, \beta, t) = v(X(\alpha, \beta, t), t)$ be the concentrations in the material coordinates $(\alpha, \beta)$. Differentiating at fixed material coordinates gives the material derivative

$$\partial_t U = \big(\partial_t u + Q \cdot \nabla_{\Omega(t)} u\big) \circ X,$$

so the Eulerian derivative is $\partial_t u = \partial_t U - Q \cdot \nabla u$ and the advection term $Q \cdot \nabla u$ cancels. The divergence of the growth field is

$$\nabla_{\Omega(t)} \cdot Q = \partial_t \log \sqrt{|\det G|},$$

and $U$, $V$ satisfy the spatially and temporally heterogeneous reaction–diffusion system on the fixed domain $\Phi$

$$\partial_t U = \frac{\delta_1}{\sqrt{|\det G|}} \sum_{i,j \in \{\alpha, \beta\}} \partial_i\!\left(\sqrt{|\det G|}\; G^{-1}_{ij}\, \partial_j U\right) - \big(\partial_t \log \sqrt{|\det G|}\big)\, U + f(U, V),$$

and likewise for $V$ with $\delta_2$ and $g$. The middle term is dilution by local area change. On the part of $\partial\Phi$ that $X$ maps onto $\partial\Omega(t)$, the boundary condition becomes

$$\sum_{i,j \in \{\alpha, \beta\}} \nu_i\, G^{-1}_{ij}\, \partial_j U = 0, \qquad \sum_{i,j \in \{\alpha, \beta\}} \nu_i\, G^{-1}_{ij}\, \partial_j V = 0,$$

where $\nu$ is the outward normal of $\Phi$ in the $(\alpha, \beta)$-plane. Edges of $\Phi$ that the parametrization identifies with each other (a periodic angle) or collapses to a point (a pole or centre) are not boundary of $\Omega(t)$ and carry no flux condition.

**Growing ellipse.** For the planar ellipse $X = (A(t)\, \alpha \cos\beta,\ B(t)\, \alpha \sin\beta,\ 0)$, $\alpha \in [0,1]$, $\beta \in [0, 2\pi]$, one finds $\det G = A^2 B^2 \alpha^2$ and a dilution rate $\dot A / A + \dot B / B$; the physical boundary is the edge $\alpha = 1$. In Cartesian material coordinates $(\xi, \eta) = (x/A, y/B)$ on the unit disk the metric is $\operatorname{diag}(A^2, B^2)$, the diffusion tensor is $\operatorname{diag}(A^{-2}, B^{-2})$, and the same pull-back reads

$$\partial_t U = \delta_1\left(\frac{1}{A(t)^2}\, \partial_\xi^2 U + \frac{1}{B(t)^2}\, \partial_\eta^2 U\right) - \left(\frac{\dot A}{A} + \frac{\dot B}{B}\right) U + f(U, V),$$

with boundary condition $\xi A^{-2} \partial_\xi U + \eta B^{-2} \partial_\eta U = 0$ on $\xi^2 + \eta^2 = 1$, and likewise for $V$. So anisotropic growth acts as direction-dependent, time-dependent effective diffusion, although this metric is diagonal. When $A \equiv B$ (an isotropically growing disk) it reduces to $\partial_t U = (\delta_1 / A^2)\, \Delta U - 2 (\dot A / A)\, U + f(U, V)$ with $\partial_\alpha U = 0$ at $\alpha = 1$, in polar material coordinates.

## Depends on

- [Laplace–Beltrami operator](../../../Geometry/riemannian-geometry/laplace-beltrami-operator/laplacian.md)

## Proof depends on

- [Jacobi's formula](../../../LinearAlgebra/determinants-and-matrix-identities/jacobi-s-formula/jacobi-det-derivative.md)

## Expansion

Reynolds' transport theorem for a material area element $\hat\Omega(t)$ of the surface, the surface analogue of [the transport theorem for a moving domain](../../../Physics/fluid-mechanics/reynolds-transport-theorem/reynolds-transport-theorem-for-a-moving-domain.md), gives $\frac{d}{dt}\int_{\hat\Omega(t)} u\, d\Omega = \int_{\hat\Omega(t)} \big(\partial_t u + \nabla \cdot (Q u)\big)\, d\Omega$, and Fick's law turns the flux into $-\delta \nabla u$; the zero-flux condition of the source is imposed on this diffusive flux at the boundary, which moves with the material. For $U = u \circ X$ the chain rule at fixed $(\alpha, \beta)$, with $\partial_t X = Q$, gives $\partial_t U = \partial_t u + Q \cdot \nabla u$, with a plus sign. Writing $\nabla \cdot (Qu) = (\nabla \cdot Q)\, u + Q \cdot \nabla u$, the Eulerian equation becomes $\partial_t U + (\nabla \cdot Q)\, U = \delta_1 \nabla^2 u + f$: the advection term is absorbed into the material derivative, and the dilution term acquires its minus sign only when it is moved to the right-hand side. The area element is $\sqrt{|\det G|}\, d\alpha\, d\beta$, so the relative rate of change of local area, which is $\nabla \cdot Q$, is $\partial_t \log \sqrt{|\det G|} = \tfrac12 \operatorname{tr}(G^{-1} \partial_t G)$ by Jacobi's formula; with a diagonal metric this reduces to $\partial_t \log(|\partial_\alpha X|\, |\partial_\beta X|)$, the form used by Plaza et al. (2004) for orthogonal growth. The Laplace–Beltrami operator in local coordinates is the standard divergence form above. In these coordinates the gradient of $u$ has components $\sum_j G^{-1}_{ij} \partial_j U$ and the outward conormal is proportional to $\sum_j G^{-1}_{ij} \nu_j$, so $\mathbf n_\partial \cdot \nabla u$ is a positive multiple of $\sum_{i,j} \nu_i G^{-1}_{ij} \partial_j U$, which gives the transformed boundary condition. For the ellipse the map $(\xi, \eta) \mapsto (A\xi, B\eta)$ is linear, so the Laplacian pulls back to $A^{-2}\partial_\xi^2 + B^{-2}\partial_\eta^2$, the outward normal of the unit disk is $(\xi, \eta)$, and the area factor $AB$ gives the dilution rate. Krause, Ellis and Van Gorder also treat a growing triaxial ellipsoid surface this way and use simulations with Schnakenberg, Gierer–Meinhardt and FitzHugh–Nagumo kinetics to compare how isotropic, staged anisotropic and fast growth affect patterns formed by [diffusion-driven instability](turing-instability.md).

## Sources

- A. L. Krause, M. A. Ellis and R. A. Van Gorder, "Influence of curvature, growth, and anisotropy on the evolution of Turing patterns on growing manifolds", Bulletin of Mathematical Biology (2018), Section 2 (Equation 2 for the model and its zero-flux boundary condition, Equations 4–17 for the general pull-back, Equations 19–26 for the ellipse), <https://doi.org/10.1007/s11538-018-0535-y> (PMC6373535).
