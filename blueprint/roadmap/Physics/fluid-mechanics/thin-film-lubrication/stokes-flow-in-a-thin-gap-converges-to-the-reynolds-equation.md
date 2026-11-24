# Stokes flow in a thin gap converges to the Reynolds equation

This node covers the derivation of the Reynolds equation of lubrication as the thin-gap limit of the steady Stokes equations. Let $h$ be
a smooth positive function on $[0, L]$, let $\mu > 0$ and real $U$ be given, and consider Stokes flow with viscosity $\mu$ in the gap
$\Omega_\varepsilon = \{(x, y) : 0 < x < L,\ 0 < y < \varepsilon h(x)\}$, driven by the lower wall moving with speed $U$, with the upper wall
at rest. In the variables $Y = y/\varepsilon$ and $P = \varepsilon^2 p$ the formal limit is a pressure $P(x)$ and, in each cross-section
$0 < Y < h(x)$, the Couette-Poiseuille profile

$$u(x, Y) = \frac{1}{2\mu}\,\frac{dP}{dx}\,\big(Y^2 - Y h(x)\big) + U\Big(1 - \frac{Y}{h(x)}\Big),$$

whose flux $\int_0^{h} u\,dY = -\frac{h^3}{12\mu}\frac{dP}{dx} + \frac{Uh}{2}$ does not depend on $x$; equivalently $P$ solves the Reynolds equation

$$\frac{d}{dx}\left(h^3\,\frac{dP}{dx}\right) = 6\mu U\,\frac{dh}{dx}.$$

A rigorous form of this limit depends on the boundary data at $x = 0$ and $x = L$, on the function spaces and on the topology of
convergence.

## Expansion

A good expansion fixes one rigorous formulation, such as that of Bayada and Chambat: the Stokes problem in $\Omega_\varepsilon$ with
prescribed velocity data on the whole boundary compatible with the wall motions, the scaled a priori estimates, and the spaces and
topologies in which the scaled velocities and pressures converge to the profile and pressure above, and states that convergence as a
theorem. The solvability of the limiting Reynolds problem with prescribed end pressures, and its explicit solution for a plane slider, are
separate nodes.

## Sources

- G. Bayada and M. Chambat, The transition between the Stokes equations and the Reynolds equation: a mathematical proof, *Applied Mathematics and Optimization* 14 (1986) 73-93.
- R. L. Panton, *Incompressible Flow*, 4th edition, Wiley, 2013, for the lubrication approximation.
