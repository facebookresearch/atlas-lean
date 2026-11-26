# Blow-up criterion and small-data global solutions for chemotaxis–Euler with Robin oxygen boundary

**Model.** In a smooth bounded domain $\Omega\subset\mathbb R^2$ with boundary $\Gamma$, consider the inviscid chemotaxis–fluid system (Tuval et al. with zero fluid viscosity)

$$n_t+u\cdot\nabla n+\nabla\cdot(n\nabla c)=\Delta n,\qquad c_t+u\cdot\nabla c+nc=\Delta c,$$

$$u_t+u\cdot\nabla u+\nabla p=-n\nabla\phi,\qquad\nabla\cdot u=0,$$

with no-flux for the bacteria, $(\nabla n-n\nabla c)\cdot\nu=0$, impermeability $u\cdot\nu=0$, and a Robin condition for oxygen exchange with the air,

$$\nabla c\cdot\nu=\kappa(x)\bigl(\gamma(x)-c\bigr)\quad\text{on }\Gamma,$$

where $\kappa,\gamma\ge0$ are given and $\gamma$ is the ambient oxygen level. For $n_0,c_0\in H^2$, $u_0\in H^3$ nonnegative and compatible, a unique local solution exists in $C([0,T];H^2\times H^2\times H^3)$.

**Theorem (blow-up criterion).** If the maximal existence time $T^*$ is finite, then

$$\|n\|_{L^q(0,T^*;L^p(\Omega))}=\infty\qquad\text{for all } \frac2p+\frac2q\le1,\ 2<p\le\infty .$$

**Theorem (global existence).** If moreover $\max\{\|\gamma\|_{L^\infty(\Gamma)},\|c_0\|_{L^\infty(\Omega)}\}\le\frac1{48}$, the solution is global, with $(n,c,u,\nabla p)\in C([0,T];H^2\times H^2\times H^3\times H^2)$ for every $T>0$.

## Expansion

Without viscosity, $u$ is controlled only through the vorticity equation, which is forced by $\nabla^\perp\cdot(n\nabla\phi)$; an $L^q_tL^p_x$ bound on $n$ (the Serrin-type condition) is enough to bound the vorticity in $L^\infty$ and close higher-order estimates, which gives the criterion. Under the Robin condition the maximum principle keeps $c\le\max\{\|c_0\|_\infty,\|\gamma\|_\infty\}$; when this level is small, the chemotactic term can be absorbed in weighted energy estimates for $n$, which give an a priori bound in the criterion's norm, so the solution never blows up.

## Depends on

- [Local well-posedness of the singular chemotaxis–Euler system](local-well-posedness-of-the-singular-chemotaxis-euler-system.md)

## Sources

- Qianqian Hou, "Global solvability to a two-dimensional chemotaxis-Euler system with Robin boundary conditions on oxygen", arXiv:2605.05740 (2026), Proposition 1.1 (local existence), Theorems 1.1 and 1.2, <https://doi.org/10.48550/arXiv.2605.05740>.
