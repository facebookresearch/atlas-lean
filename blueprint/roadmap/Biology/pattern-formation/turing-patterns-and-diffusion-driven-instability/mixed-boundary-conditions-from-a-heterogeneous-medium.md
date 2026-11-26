# Mixed boundary conditions for activator–inhibitor systems from a heterogeneous medium

Let $\Omega \subset \tilde\Omega \subset \mathbb R^2$ be smooth planar domains with $\tilde\Omega\setminus\Omega$ connected, $\Gamma = \partial\Omega$, and consider the heterogeneous two-species reaction–diffusion system with homogeneous Neumann conditions on $\partial\tilde\Omega$:

$$\partial_tu = \nabla^2u + \begin{cases} f(u,v) & x \in \Omega,\\ \rho(R - u) & x \in \tilde\Omega\setminus\Omega,\end{cases} \qquad \partial_tv = D\nabla^2v + \begin{cases} g(u,v) & x \in \Omega,\\ g_2(u,v) & x \in \tilde\Omega\setminus\Omega,\end{cases}$$

with diffusion ratio $D > 1$ (activator $u$, inhibitor $v$): outside $\Omega$ the activator relaxes to the level $R$ on the timescale $1/\rho$, while the inhibitor follows slow kinetics $g_2$ with timescale $T_{g_2}$.

**Asymptotic reduction (formal, planar).** Let $\zeta_1^*$ be the (rescaled) coordinate normal to the curve $\Gamma$ and $\zeta_2^*$ its arclength, and let $\eta$ be the ratio of the maximal thickness of $\tilde\Omega\setminus\Omega$ (normal to $\Gamma$) to the arclength of $\Gamma$. Assume the exterior region is slender and regular ($\eta \ll 1$, curvature $o(1/\eta)$, outer boundary a graph $\zeta_1^* = F(\zeta_2^*)$ with $\eta|F'| \ll 1$), the exterior inhibitor kinetics are slow compared with transverse diffusion ($\eta^2/D \ll T_{g_2}$), and $\rho^{1/2} \gg 1/\eta \gg 1$. Then, to leading order, the steady states of the heterogeneous problem are the steady states of

$$0 = \nabla^2u + f(u,v), \qquad 0 = D\nabla^2v + g(u,v) \quad \text{in } \Omega,$$

with the **mixed boundary conditions**

$$u = R, \qquad \boldsymbol n\cdot\nabla v = 0 \qquad \text{on } \partial\Omega .$$

The reduction uses the single tangential coordinate (arclength) of a boundary curve, so it is planar. In $\mathbb R^n$ with $n \ge 3$ the boundary has $n - 1$ tangential coordinates; the analogous reduction would need a separate slender-layer analysis and is not covered by this statement.

Choosing $R$ near the minimum of the activator in a Neumann pattern (below the homogeneous steady state) selects steady states whose patterns are isolated away from the boundary.

## Depends on

- [Diffusion-driven instability (Turing 1952)](turing-instability.md)

## Expansion

Across $\Gamma$ a pillbox argument gives continuity of $u, v$ and of their normal fluxes. In the slender exterior, $v_{\zeta_1^*\zeta_1^*} = 0$ with a no-flux outer wall forces $v$ to be constant across the layer, so flux continuity gives $\partial_nv = 0$ on $\Gamma$. For $u$, the exterior equation $u_{\zeta_1^*\zeta_1^*} + \eta^2\rho(R-u) = 0$ has solution $u = R + A\cosh\big(\rho^{1/2}\eta(F - \zeta_1^*)\big)$; bounded flux at $\Gamma$ forces $|A| = O\big(\rho^{-1/2}/\sinh(\rho^{1/2}\eta F)\big)$, so $u = R + O(\rho^{-1/2})$ throughout the exterior, and continuity gives the Dirichlet condition $u = R$. Transient dynamics of the two problems may differ even though their steady states agree.

## Sources

- Andrew L. Krause, Václav Klika, Philip K. Maini, Denis Headon and Eamonn A. Gaffney, "Isolating Patterns in Open Reaction–Diffusion Systems", Bulletin of Mathematical Biology 83 (2021), 82, <https://doi.org/10.1007/s11538-021-00913-4> (PMC8178156). Section 2.1, Eqs. (1)–(12); Section 2.2.
