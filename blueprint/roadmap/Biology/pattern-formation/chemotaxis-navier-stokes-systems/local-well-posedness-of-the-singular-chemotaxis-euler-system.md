# Local well-posedness of the singular chemotaxis–Euler system

**Model.** Chemotaxis with logarithmic sensitivity in a fluid on the half-plane $\{y>0\}$ reads

$$\partial_t n-\Delta n+u\cdot\nabla n+\nabla\cdot\Bigl(\frac nc\nabla c\Bigr)=0,\qquad \partial_t c-\varepsilon\Delta c+u\cdot\nabla c+nc=0,$$

$$\partial_t u-\varepsilon\Delta u+(u\cdot\nabla)u+\nabla p=n e_2,\qquad\nabla\cdot u=0 .$$

The Cole–Hopf-type substitution $v=-\nabla\ln c$ removes the singularity at $c=0$ and gives

$$\partial_t n-\Delta n+u\cdot\nabla n-\nabla\cdot(nv)=0,\qquad \partial_t v-\varepsilon\Delta v+\nabla(u\cdot v)+\nabla(\varepsilon|v|^2-n)=0,$$

together with the Navier–Stokes equation for $u$; curl-free $v$ stays curl-free. At $\varepsilon=0$ the $v$ and $u$ equations lose their diffusion and the system becomes the *supercritical chemotaxis–Euler system*

$$\partial_t v+\nabla(u\cdot v)-\nabla n=0,\quad \nabla\times v=0,\qquad \partial_t u+u\cdot\nabla u+\nabla p=ne_2,\quad\nabla\cdot u=0,$$

with boundary conditions $\partial_y n+nv_2=0$ and $u_2=0$ on $y=0$.

**Theorem.** Let $m\ge2$ and let $(n_{in},v_{in},u_{in})\in H^m\times H^m\times H^{m+1}$ with $n_{in}\ge0$, $\nabla\times v_{in}=0$ and the compatibility conditions at $y=0$. Then there is $T>0$ such that the $\varepsilon=0$ system has a unique solution on $[0,T]$ with

$$\|n\|_{L^\infty_tH^m}^2+\|v\|_{L^\infty_tH^m}^2+\|u\|_{L^\infty_tH^{m+1}}^2+\|n\|_{L^2_tH^{m+1}}^2\le C,$$

and, for $0<2j\le m$, $\partial_t^jn,\partial_t^jv\in L^\infty_tH^{m-2j}$ and $\partial_t^ju\in L^\infty_tH^{m+1-2j}$.

## Expansion

Only the cell density keeps its diffusion at $\varepsilon=0$. The $n$–$v$ coupling is of hyperbolic–parabolic type: differentiating, $\nabla n$ enters the $v$ equation with a favourable sign, so the energy $\int(|\partial^\alpha v|^2 n+\ldots)$-type symmetrization closes with one derivative of smoothing from $\Delta n$. The fluid is a forced Euler flow in $H^{m+1}$. This well-posedness result is the outer (leading-order) profile in the boundary-layer expansion of the viscous system with Navier-slip conditions, where inner layers of width $\sqrt\varepsilon$ correct the lost boundary conditions for $v$ and $u$.

## Depends on

- [Vanishing viscosity limit of chemotaxis–Navier–Stokes with a slip boundary](vanishing-viscosity-limit-of-chemotaxis-navier-stokes-with-slip-boundary.md)

## Sources

- Hui Wang, Wendong Wang and Lingling Zhao, "Boundary layer analysis for the 2D chemotaxis-Navier-Stokes system with logarithmic sensitivity, Part I: Well-posedness", arXiv:2608.05940 (2026), Section 2, Theorems 2.1 and 2.2, <https://doi.org/10.48550/arXiv.2608.05940>.
