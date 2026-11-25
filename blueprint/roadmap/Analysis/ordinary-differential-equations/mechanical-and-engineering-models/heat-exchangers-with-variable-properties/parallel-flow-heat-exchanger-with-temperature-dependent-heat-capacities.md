# Parallel-flow heat exchanger with temperature-dependent heat capacities

This node covers the steady parallel-flow exchanger with variable specific heats. Let $\dot m_h, \dot m_c, U, P, L > 0$ and let $c_h, c_c$
be positive Lipschitz functions of temperature. Consider on $[0, L]$

$$\dot m_h c_h(T_h)\,T_h' = -UP\,(T_h - T_c), \qquad \dot m_c c_c(T_c)\,T_c' = UP\,(T_h - T_c),$$

with $T_h(0) > T_c(0)$. There is exactly one solution on $[0, L]$; along it $T_h$ is strictly decreasing, $T_c$ strictly increasing, and
$T_h - T_c$ is positive and strictly decreasing. With $H_h' = \dot m_h c_h$ and $H_c' = \dot m_c c_c$, the energy balance
$H_h(T_h(0)) - H_h(T_h(L)) = H_c(T_c(L)) - H_c(T_c(0))$ holds, and the transferred heat is less than the smaller of the two streams' enthalpy
changes on cooling or heating to the other stream's inlet temperature.

## Expansion

A good expansion proves existence and uniqueness by Picard-Lindelöf with a priori bounds from the monotonicity, positivity of the
temperature difference from a linear differential inequality, and the energy balance by adding the two equations. Phase-changing streams,
counterflow (a boundary-value problem) and effectiveness correlations are separate nodes; the constant-property parallel-flow, counterflow
and effectiveness results are their own pages.

## Sources

- T. L. Bergman, A. S. Lavine, F. P. Incropera and D. P. DeWitt, *Fundamentals of Heat and Mass Transfer*, 7th edition, Wiley, 2011, for heat-exchanger analysis.
