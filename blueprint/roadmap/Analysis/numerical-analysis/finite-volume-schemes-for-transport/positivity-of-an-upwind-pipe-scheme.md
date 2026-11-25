# Positivity of an upwind pipe scheme

Take $N \ge 2$ cells of width $\Delta x > 0$, time step $\Delta t > 0$, velocity $a \ge 0$, diffusivity $D \ge 0$ and no reaction,
with inlet concentration $g \ge 0$ and zero diffusive gradient at the outlet. The face fluxes are
$F_0 = a g - D (u_0 - g)/\Delta x$ at the inlet, $F_{i+1} = a u_i - D (u_{i+1} - u_i)/\Delta x$ at the interior faces and
$F_N = a u_{N-1}$ at the outlet, and the update is $u_i^+ = u_i - \frac{\Delta t}{\Delta x}(F_{i+1} - F_i)$. With
$\nu = a\Delta t/\Delta x$ and $\mu = D\Delta t/\Delta x^2$, every $u_i^+$ is a combination of $u_{i-1}, u_i, u_{i+1}$ and $g$ with
nonnegative coefficients when $\nu + 2\mu \le 1$, so nonnegative data stay nonnegative; and the inventory identity of the
nonperiodic scheme holds with these boundary fluxes. The scheme is not periodic, and implicit schemes, convergence and reaction
steps are outside this result.

## Depends on

## Proof depends on

- [Inventory of a nonperiodic finite-volume scheme](inventory-of-a-nonperiodic-finite-volume-scheme.md), for the inventory identity

## Sources

- L. R. Hellevik, *Numerical Methods for Engineers*, NTNU, Section 7.3, criterion for positive coefficients, Equations 7.18–7.21, <https://leifh.folk.ntnu.no/teaching/tkt4140/>.
- *Numerical Methods I* lecture notes, University of Münster, Chapter 2 (advection equation), Section 2.2, upwind schemes and the CFL condition (2.7), <https://www.uni-muenster.de/imperia/md/content/physik_tp/lectures/ws2016-2017/num_methods_i/advection.pdf>.
