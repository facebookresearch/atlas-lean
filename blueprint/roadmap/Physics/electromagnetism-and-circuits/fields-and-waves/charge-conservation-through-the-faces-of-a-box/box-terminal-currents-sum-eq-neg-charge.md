# Box terminal flux balance

Terminal outward currents identified
with the six outward face fluxes of the box `Set.Icc a b` sum to minus
the integral of the charge-density rate `ρdot` over the box, which is the
enclosed-charge rate by `hasDerivAt_enclosedCharge`, under the local
continuity law `ρdot + div J = 0`. The `chargeContinuity` premise of
`sum_terminalCurrent_eq_neg_chargeRate` is discharged by the divergence
theorem rather than assumed.
