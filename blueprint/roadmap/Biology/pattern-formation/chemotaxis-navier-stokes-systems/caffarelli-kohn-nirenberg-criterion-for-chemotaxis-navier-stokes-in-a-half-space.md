# Caffarelli–Kohn–Nirenberg criterion for chemotaxis–Navier–Stokes in a half-space

**Model.** In the half-space $\mathbb H^3=\{x\in\mathbb R^3: x_3>0\}$ consider the chemotaxis–Navier–Stokes system for a cell density $n\ge 0$, an oxygen concentration $c\ge 0$, a velocity $u$ and a pressure $p$:

$$\partial_t n+u\cdot\nabla n-\Delta n=-\nabla\cdot(n\nabla c),\qquad \partial_t c+u\cdot\nabla c-\Delta c=-nc,$$

$$\partial_t u+u\cdot\nabla u-\Delta u+\nabla p=-n\nabla\phi,\qquad \nabla\cdot u=0,$$

with no-slip ($u=0$) and no-flux ($\partial_{x_3}n=\partial_{x_3}c=0$) conditions on $\{x_3=0\}$, where the gravitational potential $\phi$ is time independent with $M_\phi=\|\nabla\phi\|_{L^\infty}<\infty$, and $M_c$ bounds $\|c\|_{L^\infty}$. A point is *regular* if the solution is Hölder continuous in a parabolic neighborhood of it; $\tilde c$ is the normalized oxygen variable used in the local entropy–energy inequality.

**Theorem (dissipation criterion).** There is $\varepsilon_3=\varepsilon_3(M_c,M_\phi)>0$ such that, for every suitable weak solution on $\mathbb H^3\times(0,\infty)$, a point $z_0=(x_0,t_0)\in\overline{\mathbb H^3}\times(0,\infty)$ is regular whenever

$$\limsup_{r\downarrow 0}\frac1r\int_{\mathcal Q_r(z_0)}\Bigl(|\nabla\sqrt n|^2+|\nabla^2\sqrt{\tilde c}|^2+|\nabla u|^2\Bigr)\,dx\,dt\le\varepsilon_3,$$

where $\mathcal Q_r(z_0)$ is the parabolic cylinder (interior points) or half-cylinder (boundary points) of radius $r$.

**Corollary (size of the singular set).** For every global suitable weak solution, the space–time singular set $\mathcal S\subset\overline{\mathbb H^3}\times(0,\infty)$, boundary points included, has vanishing one-dimensional parabolic Hausdorff measure: $\mathcal P^1(\mathcal S)=0$.

**Existence.** For $n_0\ge0$ with $n_0, n_0\log n_0\in L^1$, $c_0\in L^1\cap L^\infty$ with $\nabla\sqrt{c_0}\in L^2$, and divergence-free $u_0\in L^2$, a global suitable weak solution exists.

## Expansion

The proof follows the Caffarelli–Kohn–Nirenberg scheme for Navier–Stokes: an $\varepsilon$-regularity statement under smallness of scale-invariant energy and pressure quantities on a unit cylinder, upgraded to the endpoint $r^{-1}$ dissipation scaling by an iteration. The chemotactic coupling is controlled through the entropy–energy functional $\int n\log n+\tfrac12|\nabla\sqrt c|^2$-type quantities and a weighted mass bound, which absorbs the extra mass term that appears after rescaling. Boundary points need pressure and caloric decompositions compatible with the no-slip and no-flux conditions. A Vitali covering argument then turns the criterion into $\mathcal P^1(\mathcal S)=0$, the same size bound as for the three-dimensional Navier–Stokes equations.

## Sources

- Yubo Chen and Jianbo Yu, "Global Existence and Partial Regularity for the Three-Dimensional Chemotaxis–Navier–Stokes System in a Half-Space", arXiv:2610.13613 (2026), Theorem 1.1, Theorem 1.2 and Corollary 1.3, <https://doi.org/10.48550/arXiv.2610.13613>.
