# Rotor current of the induction machine Thevenin model

For a complex Thevenin voltage `V_th` and real `R_th`, `R₂`, `X_eq` and slip `s`, the rotor current
is `I₂ = V_th s / (R_th s + R₂ + i X_eq s)`. For `s ≠ 0` it is `V_th / (R_th + R₂ / s + i X_eq)`,
the Thevenin voltage over the impedance with real part `R_th + R₂ / s` and reactance `X_eq`
([quotient form](rotor-current-eq-div.md)); at `s = 0`, synchronous speed, it is `0`
([zero slip](rotor-current-zero-slip.md)). With the convention `z / 0 = 0` it is also `0` where
`R_th s + R₂ = 0` and `X_eq s = 0`. In the model the rotor resistance `R₂` and the synchronous speed
`ω_s` are positive and the Thevenin resistance `R_th` is nonnegative; the slip is in `(0, 1]` for a
motor.
