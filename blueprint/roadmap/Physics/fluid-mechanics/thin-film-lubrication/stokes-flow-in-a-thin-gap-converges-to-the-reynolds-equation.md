# Stokes flow in a thin gap converges to the Reynolds equation

This node covers the rigorous justification of the Reynolds lubrication equation. Let $h$ be a smooth positive function on $[0, L]$ and
$\Omega_\varepsilon = \{(x, y) : 0 < x < L,\ 0 < y < \varepsilon h(x)\}$. Let $(u_\varepsilon, p_\varepsilon)$ solve the steady Stokes equations with
viscosity $\mu > 0$ in $\Omega_\varepsilon$, with velocity $(U, 0)$ on the lower wall $y = 0$, no slip on the upper wall and the boundary
conditions at $x = 0$ and $x = L$ that fix the pressure there to zero in the limit. After the scaling $y = \varepsilon Y$ and
$p_\varepsilon = \varepsilon^{-2} P_\varepsilon$, the rescaled pressures $P_\varepsilon$ converge, as $\varepsilon \to 0$, to the unique solution
$P$ of the Reynolds equation

$$\frac{d}{dx}\left(h^3\,\frac{dP}{dx}\right) = 6\mu U\,\frac{dh}{dx}, \qquad P(0) = P(L) = 0,$$

and the rescaled velocities converge to the corresponding Couette-Poiseuille profile in each cross-section.

## Expansion

A good expansion fixes the exact lateral boundary conditions and function spaces of the cited proof, states the scaled a priori
estimates, and then the convergence in the norms the source uses. The solvability of the limiting Reynolds problem, and its explicit
solution for a plane slider, are separate nodes; only the convergence is this node's claim.

## Sources

- G. Bayada and M. Chambat, The transition between the Stokes equations and the Reynolds equation: a mathematical proof, *Applied Mathematics and Optimization* 14 (1986) 73-93.
- R. L. Panton, *Incompressible Flow*, 4th edition, Wiley, 2013, for the lubrication approximation.
