# Post-pulse drift at a stable rest state

In the classical regime `0 < b < 1`, `ε > 0`, at
an equilibrium on the left branch `-2 ≤ v < -1` the Jacobian is Hurwitz and `pulseRootLow v` is
positive: the voltage falls after pulses `0 < δ < pulseRootLow v` and rises after pulses
`pulseRootLow v < δ < pulseRootHigh v`. At the endpoint `v = -2` the two roots coincide
(`pulseRootLow (-2) = pulseRootHigh (-2) = 3`), so the last statement is vacuous and the voltage
rises after no positive pulse; `stable_rest_rising_pulse_window` treats `-2 < v < -1`.
