# Vanishing viscosity limit of chemotaxis–Navier–Stokes with a slip boundary

**Model.** In the half-plane $\{(x,y): y>0\}$ consider the chemotaxis–Navier–Stokes system in which the oxygen diffusivity and the fluid viscosity are both $\varepsilon^2$ while the bacteria keep unit diffusivity:

$$\partial_t n^\varepsilon+u^\varepsilon\cdot\nabla n^\varepsilon-\Delta n^\varepsilon=-\nabla\cdot(n^\varepsilon\nabla c^\varepsilon),\qquad \partial_t c^\varepsilon+u^\varepsilon\cdot\nabla c^\varepsilon-\varepsilon^2\Delta c^\varepsilon=-c^\varepsilon n^\varepsilon,$$

$$\partial_t u^\varepsilon+u^\varepsilon\cdot\nabla u^\varepsilon-\varepsilon^2\Delta u^\varepsilon+\nabla p^\varepsilon=n^\varepsilon e_2,\qquad\nabla\cdot u^\varepsilon=0,$$

with $\partial_y n^\varepsilon=\partial_y c^\varepsilon=0$ and slip conditions $\partial_y u_1^\varepsilon=u_2^\varepsilon=0$ on $y=0$. At $\varepsilon=0$ the limit is a chemotaxis–Euler system whose oxygen equation has no diffusion.

**Theorem.** Let the initial data lie in $H^9$ and satisfy the compatibility conditions, and let $(n^a,c^a,u^a)$ be the approximate solution

$$n^a=n^{e,0}+\varepsilon n^{b,1}+\varepsilon^2n^{b,2},\quad c^a=c^{e,0}+\varepsilon c^{b,1}+\varepsilon^2c^{b,2},\quad u_1^a=u_1^{e,0}+\varepsilon u_1^{b,1},\quad u_2^a=u_2^{e,0}+\varepsilon^2u_2^{b,2},$$

built from the inviscid outer solution $(n^{e,0},c^{e,0},u^{e,0})$ and boundary-layer correctors depending on the fast variable $z=y/\varepsilon$. Then there are $\varepsilon_0,T,C>0$ independent of $\varepsilon$ such that for $0<\varepsilon<\varepsilon_0$ the error $(n,c,u)=(n^\varepsilon-n^a,c^\varepsilon-c^a,u^\varepsilon-u^a)$ exists uniquely on $[0,T]$ in the conormal space $Y^{1,2}$ and

$$\sup_{0\le t\le T}\|(n,c,u)(t)\|_{L^2\cap L^\infty}\le C\varepsilon^{3/2}.$$

In particular $(n^\varepsilon,c^\varepsilon,u^\varepsilon)$ converges to the chemotaxis–Euler solution in $L^\infty$, uniformly on $[0,T]$, at rate $O(\varepsilon)$.

## Expansion

The boundary layer has width $\varepsilon$, matching the diffusion length of $c$ and $u$. Under the slip condition the layer amplitude is $O(\varepsilon)$ (no Prandtl-type $O(1)$ layer), so the correctors can be built explicitly from linear heat-type problems in $z$. The error equations are closed by energy estimates in anisotropic conormal Sobolev spaces, where tangential derivatives and the weighted normal derivative $\frac{y}{1+y}\partial_y$ commute with the boundary conditions; vorticity estimates control the normal derivative of $u$.

## Sources

- Bolun Li, Fengqiang Shi and Wendong Wang, "Zero-viscosity limit of the chemotaxis-Navier-Stokes equations with the Navier-slip boundary condition", arXiv:2605.02394 (2026), Section 2, Proposition 2.1 and Theorem 2.2, <https://doi.org/10.48550/arXiv.2605.02394>.
