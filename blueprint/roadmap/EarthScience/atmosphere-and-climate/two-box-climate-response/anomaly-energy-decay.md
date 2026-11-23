# Anomaly energy decay

Anomaly-energy decay: if `xs, xd` satisfy the anomaly ODEs
`Cs*xs' = -lam*xs - gam*(xs - xd)` and `Cd*xd' = gam*(xs - xd)` at `t`,
then `E(t) = (Cs*xs^2 + Cd*xd^2)/2` satisfies `E'(t) <= -c * E(t)` with
`c = min (2*lam/(Cs + 2*Cd)) (gam/Cd) > 0`. Combines
`anomaly_energy_hasDerivAt` with `anomaly_energy_dissipation_bound`.
