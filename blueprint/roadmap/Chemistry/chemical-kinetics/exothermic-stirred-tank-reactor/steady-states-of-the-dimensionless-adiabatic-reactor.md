# Steady states and an energy invariant of the dimensionless adiabatic reactor

Let $a \in \mathbb{R}$, $b > 0$ and $\beta \ge 0$, and put $k(T) = e^{a - b/T}$ for $T > 0$. Consider the
dimensionless adiabatic stirred-tank reactor

$$c' = 1 - c - k(T)\,c, \qquad T' = 1 - T + \beta\,k(T)\,c,$$

with concentration $c$ and temperature $T > 0$, both scaled by their feed values and with time scaled by the
dilution rate.

1. A state $(c, T)$ with $T > 0$ is a steady state if and only if $c = 1/(1 + k(T))$ and
   $g_\beta(T) = 1 + \beta\,k(T)/(1 + k(T)) - T = 0$.
2. Along every solution with $T > 0$, the quantity $Z = T + \beta c$ satisfies $Z' = 1 + \beta - Z$.
3. If $c(0) \in [0, 1]$ and $T(0) > 0$, the solution exists for all $t \ge 0$, and for all $t \ge 0$

    $$0 \le c(t) \le 1, \qquad \min(T(0), 1) \le T(t) \le \max\bigl(Z(0), 1 + \beta\bigr).$$

Part 1 is the elimination of $c$ from the two steady-state equations. Part 2 adds $\beta$ times the first equation
to the second. In part 3, $c' = 1 > 0$ at $c = 0$ and $c' = -k(T) < 0$ at $c = 1$, so $[0, 1]$ is invariant for $c$;
then $T' \ge 1 - T$ gives the lower bound, and $T \le Z \le \max(Z(0), 1 + \beta)$ by part 2. Global existence is the
existence theorem for the Arrhenius reactor with dilution rate $1$, feed concentration and temperature $1$,
prefactor $e^a$, activation temperature $b$, heat-release coefficient $\beta$ and no cooling.

## Depends on

## Proof depends on

- [Global forward existence of the Arrhenius reactor path](exists-arrhenius-path.md), for existence on $[0, \infty)$ with no cooling

## Sources

- J. B. Rawlings and J. G. Ekerdt, *Chemical Reactor Analysis and Design Fundamentals*, 2nd edition, paperback, seventh printing (November 2026), Nob Hill Publishing; freely distributed by the authors at <https://sites.engineering.ucsb.edu/~jbraw/chemreacfun/> (page numbers below are the printed ones): Section 6.3.1, Equation 6.37 and the steady-state energy balance of the adiabatic reactor with Table 6.1 (pp. 288–289). The dimensionless variables are those of the nondimensionalization page in this folder.
