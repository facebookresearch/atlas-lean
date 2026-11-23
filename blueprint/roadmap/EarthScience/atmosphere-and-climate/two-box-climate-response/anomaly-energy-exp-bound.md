# Anomaly energy exp bound

Anomaly-energy exponential bound: if `xs, xd` satisfy the anomaly ODEs
`Cs*xs' = -lam*xs - gam*(xs - xd)` and `Cd*xd' = gam*(xs - xd)` at every
`t >= 0`, with derivatives taken within `[0, ∞)` (so only the forward
trajectory matters, and `t = 0` needs only a right derivative), then
`E(t) = (Cs*xs^2 + Cd*xd^2)/2` satisfies `E(t) <= exp(-c*t) * E(0)` for
`t >= 0`, with `c = min (2*lam/(Cs + 2*Cd)) (gam/Cd) > 0`. The energy
derivative is computed as in `anomaly_energy_hasDerivAt`, within `[0, ∞)`;
with `anomaly_energy_dissipation_bound`, `le_exp_mul_of_hasDerivWithinAt_Ici`
gives the bound.
