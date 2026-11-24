# Pulse Root Low

The lower root `(-3v - √(12 - 3v²))/2` of the post-pulse factor `1 - v² - v δ - δ²/3` in `δ`
(`pulse_factor`, for `v² ≤ 4`): from a rest state with voltage `v`, a pulse of this amplitude
lands on the voltage nullcline. On the left branch `-2 < v < -1` it is positive, and the positive
pulses after which the voltage rises are exactly those with
`pulseRootLow v < δ < pulseRootHigh v` (`isRisingAfterPulse_iff`), a nonempty open interval
(`pulseRootLow_lt_pulseRootHigh`).
