# Thermal efficiency of the ideal Rankine cycle

This node covers the energy accounting of the ideal Rankine cycle. A working fluid of mass flow rate $\dot m > 0$ passes in steady
flow through an adiabatic reversible pump (states 1 to 2), a boiler at constant pressure (2 to 3), an adiabatic reversible turbine (3 to 4)
and a condenser at constant pressure (4 to 1), with negligible kinetic and potential energy changes, and with specific enthalpies $h_i$ and
entropies $s_i$ at the four states, so $s_2 = s_1$ and $s_4 = s_3$. Then the net work and heat input per unit mass are
$w_{\mathrm{net}} = (h_3 - h_4) - (h_2 - h_1)$ and $q_{\mathrm{in}} = h_3 - h_2$, and if $q_{\mathrm{in}} > 0$ the thermal efficiency is

$$\eta = \frac{(h_3 - h_4) - (h_2 - h_1)}{h_3 - h_2} .$$

If $0 < T_C \le T_H$ are absolute temperatures, the heat is received at temperatures at most $T_H$ and rejected at temperatures at least $T_C$, and the cycle satisfies the Clausius inequality $q_{\mathrm{in}}/T_H - q_{\mathrm{out}}/T_C \le 0$ with $q_{\mathrm{out}} = h_4 - h_1$, then $\eta \le 1 - T_C/T_H$.

## Depends on

- [Efficiency of an engine is at most the Carnot efficiency](../entropy-heat-engines-and-the-third-law/engine-efficiency-le-carnot-efficiency.md)

## Expansion

A good expansion applies the steady-flow energy balance to each component and the entropy balance to the reversible
adiabatic ones, then compares the cycle with the Carnot bound by the Clausius inequality. The phase-equilibrium property relations that
give the state values (saturation, quality, superheat) are separate inputs, as are vapour-compression refrigeration cycles.

## Sources

- M. J. Moran and H. N. Shapiro, *Fundamentals of Engineering Thermodynamics*, 6th edition, Wiley, 2008, for vapour power cycles.
