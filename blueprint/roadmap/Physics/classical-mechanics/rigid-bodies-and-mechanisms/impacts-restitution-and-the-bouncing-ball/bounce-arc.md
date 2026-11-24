# Arc and event

For `m > 0` and `g > 0`, an active arc `n` (`IsActiveArc`: take-off speed
`u_n > 0`), the constant-force trajectory from the floor with take-off speed `u_n` under the weight
`-(m g)`, has the positive duration `T_n`, is back on the floor at `T_n`, stays above it on
`(0, T_n)` and arrives with velocity `-u_n`; the fixed-wall event applied to that arrival velocity
gives the take-off speed `u_(n+1)` of the next arc. For `e > 0` and `u₀ > 0` every arc is active
(`isActiveArc_of_pos`); for `e = 0` only the first one is (`inelastic_stops`).
