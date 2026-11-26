# Inventory of a nonperiodic finite-volume scheme

Let cells $i = 0, \dots, N - 1$ have widths $\Delta x_i > 0$ and averages $u_i$, and let a conservative explicit step of length
$\Delta t > 0$ for one-dimensional advection, diffusion and reaction be
$u_i^+ = u_i - \frac{\Delta t}{\Delta x_i}(F_{i+1} - F_i) + \Delta t\, r_i$, with face fluxes $F_0$ (inflow boundary), $F_1, \dots,
F_{N-1}$ (interior) and $F_N$ (outflow boundary) and reaction terms $r_i$. Then the width-weighted inventory changes by

$$\sum_i \Delta x_i u_i^+ - \sum_i \Delta x_i u_i = \Delta t\,(F_0 - F_N) + \Delta t \sum_i \Delta x_i r_i.$$

This is the finite-volume ledger with wells applied with common volume $1$, cell values $\Delta x_i u_i$ and well rates
$\Delta x_i r_i$: multiplying the update by $\Delta x_i$ gives
$\Delta x_i u_i^+ = \Delta x_i u_i + \Delta t\,\bigl(-(F_{i+1} - F_i) + \Delta x_i r_i\bigr)$. Omitting the widths breaks this identity on
unequal cells.
Convergence is outside this result.

## Depends on

## Proof depends on

- [Finite-volume ledger with wells](../../../EarthScience/hydrology-and-surface-processes/part-02/radial-flow-to-wells-well-sources-and-fractional/stock-add-mul-well-cell-rate.md)

## Sources

- *Numerical Methods I* lecture notes, University of Münster, Chapter 2 (advection equation), Section 2.2, upwind schemes and the CFL condition (2.7), <https://www.uni-muenster.de/imperia/md/content/physik_tp/lectures/ws2016-2017/num_methods_i/advection.pdf>.
