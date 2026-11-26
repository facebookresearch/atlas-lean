# Torque–slip curve of the induction machine

For a complex `V_th` and real `R_th`, `R₂`, `X_eq`, `ω_s` and `s`, the torque curve is
`T(s) = 3 ‖V_th‖² R₂ s / (ω_s ((R_th s + R₂)² + (X_eq s)²))`, the rational function of the slip
obtained by clearing the slip division in the current. For `R₂ > 0`, `ω_s > 0`, `R_th ≥ 0` and
`0 < s ≤ 1` it equals the [developed torque](developed-torque-eq-torque-curve.md) of the model rotor
current. Its value at `s = 0` is `0`, since the numerator vanishes. With the convention `x / 0 = 0`
it is also `0` where the denominator vanishes. In the model the rotor resistance `R₂` and the
synchronous speed `ω_s` are positive and the Thevenin resistance `R_th` is nonnegative; the slip is
in `(0, 1]` for a motor.
