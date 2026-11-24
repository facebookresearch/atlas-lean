# Guarded friction loss: positive coefficient, power and reversal

Let a [friction correlation](friction-correlation.md) `C`
[apply as a Darcy factor](darcy-applies.md) to a [request](friction-request.md) `r`, with a positive
[Darcy factor](darcy-factor.md) `f`. Let `L`, `D`, `A`, `ρ` and `μ` be positive and `Q` and `ε`
real, and suppose the request's Reynolds number is that of the flow, `Re = ρ |Q / A| D / μ`, and its
relative roughness is that of the pipe, `ε / D`. Then:

- the correlation was calibrated for the pipe's relative roughness `ε / D`;
- the [loss coefficient](darcy-coefficient.md) `c = f L ρ / (2 D A²)` is positive;
- the reversed flow `-Q` has the same Reynolds number, `Re = ρ |-Q / A| D / μ`, so the same
  factor applies to it in the same pipe;
- the dissipated power `Δp Q` of the [pressure drop](friction-pressure-drop.md)
  `Δp = c Q |Q|` is nonnegative;
- the reversed flow has the pressure drop `-Δp`.
