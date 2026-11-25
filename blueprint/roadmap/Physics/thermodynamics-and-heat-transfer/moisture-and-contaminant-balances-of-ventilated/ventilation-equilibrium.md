# Equilibrium concentration of a well-mixed ventilated room

For a volumetric flow `Q`, an outdoor concentration `c_out` and a constant indoor source `G` (mass
per time), the ventilation equilibrium is

`c_eq = c_out + G/Q`.

It is meant for `Q > 0`; with `x/0 = 0` it is `c_out` when `Q = 0`. For `V > 0` and `Q > 0` it is
the [steady amount](steady-amount-eq-ventilation-equilibrium.md) `R/k` of the compartment equation
of a room of volume `V`, at the rate `k = Q/V` and the input `R = (Q c_out + G)/V`. Concentrations
are mass per volume in one consistent unit; a ppm figure must be converted first.
