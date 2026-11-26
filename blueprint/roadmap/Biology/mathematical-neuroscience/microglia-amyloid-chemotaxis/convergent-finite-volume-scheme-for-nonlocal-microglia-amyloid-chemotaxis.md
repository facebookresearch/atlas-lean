# Convergent finite-volume scheme for nonlocal microglia–amyloid chemotaxis with measure-valued vascular influx

**Model.** In a bounded polygonal ($d=2$) or polyhedral ($d=3$) domain $\Omega$, an activated microglial density $u$ moves toward a soluble amyloid-$\beta$-associated signal $v$ by nonlocal sensing:
$$\begin{cases}
\partial_tu-D_u\Delta u+\chi\nabla\cdot\big(u\,\nabla\mathcal K_\sigma[v]\big)=\mathcal R_u(x,t,u,v),\\
\partial_tv-D_v\Delta v=\mathcal R_v(x,t,u,v),
\end{cases}\qquad \mathcal K_\sigma[v]\,(x)=\int_\Omega K_\sigma(x,y)v(y)\,dy .$$
Here $\sigma>0$ is a fixed sensing length. The reactions model recruitment and saturating activation of microglia, their loss, signal production and decay, and microglia-mediated clearance of the signal; all parameters are nonnegative and the data are bounded. The signal enters through a vascular part $\Gamma_{\rm v}$ of the boundary, a union of boundary faces, as a nonnegative **Radon measure** flux $D_v\partial_\nu v=\mu$ on $\Gamma_{\rm v}\times(0,T)$. Elsewhere the boundary conditions are no-flux. For each $\sigma>0$, the regularity of the kernel makes $v\mapsto b_\sigma[v]=\nabla\mathcal K_\sigma[v]$ map finite signal mass to a bounded, spatially Lipschitz velocity field.

**Scheme.** Use a fully implicit two-point finite-volume discretization with upwind chemotactic fluxes driven by a discrete nonlocal potential $K_{\sigma,\mathcal D}[v]$. The boundary source enters through its exact mass $\mu(F\times(t^k,t^{k+1}])$ on each boundary face–time cell.

**Theorem.**

1. For nonnegative initial data the scheme has at least one nonnegative solution at every time step, with no restriction on $\Delta t$.
2. Discrete solutions satisfy mass, energy and discrete-gradient bounds and compactness estimates that are uniform in the mesh.
3. Let $1<q<q_*=\frac{d+2}{d+1}$ and consider a uniformly regular sequence of admissible meshes resolving the boundary faces, with $h+\Delta t\to0$. Then any sequence of discrete solutions has a subsequence converging (with $v$ converging in $L^q$-type spaces, as dictated by the measure data) to a nonnegative weak solution of the continuous problem. In particular, weak solutions exist.

## Expansion

A measure-valued Neumann flux makes $v$ only as regular as the Green function of the heat equation with boundary measure data. This gives the Boccardo–Gallouët-type integrability $\nabla v\in L^q$ for $q<(d+2)/(d+1)$, so the weak formulation uses test functions in $C^1$ in time and $C^2$ in space. Nonlocal sensing is what makes the problem tractable: $\nabla\mathcal K_\sigma[v]$ is bounded and Lipschitz as soon as $v$ has finite mass, so the cross-diffusion term needs no gradient control of $v$ and Keller–Segel blow-up is excluded for fixed $\sigma$. Implicit upwinding preserves positivity unconditionally, exact face–time masses keep the discrete source consistent with an arbitrary measure, and consistency of the discrete gradients and nonlocal reconstructions lets the limit pass in every term.

## Sources

- Elmahdi Erraji, "Convergence Analysis of a Finite-Volume Scheme for a Microglia--Amyloid Chemotaxis Model with Measure-Valued Vascular Boundary Sources", arXiv:2608.04785 (2026), Section 1 (model), Assumption 2.1 (data), Section 3 (finite-volume scheme, Proposition 3.2, Theorem 3.7) and Appendix (Propositions A.1–A.2 on consistency), <https://doi.org/10.48550/arXiv.2608.04785>.
