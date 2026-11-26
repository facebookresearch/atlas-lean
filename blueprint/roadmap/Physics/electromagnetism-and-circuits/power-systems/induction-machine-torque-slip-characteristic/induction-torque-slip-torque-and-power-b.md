# Torque–slip curve and power balance on the motoring range

Let `R₂ > 0`, `ω_s > 0`, `R_th ≥ 0`, `X_eq` real, `V_th` complex and `0 < s ≤ 1` (the motoring range
of the slip), and let `I₂` be the [rotor current](rotor-current.md)
`I₂ = V_th s / (R_th s + R₂ + i X_eq s)`. Then:

- the [developed torque](developed-torque.md) is
  `T(s) = 3 ‖V_th‖² R₂ s / (ω_s ((R_th s + R₂)² + (X_eq s)²))`;
- the [torque curve](torque-curve.md) takes the value `0` at slip `0` and is continuous there;
- the [converted power](converted-power.md) is `(1 - s)` times the [air-gap power](air-gap-power.md)
  and equals the developed torque times the rotor speed `(1 - s) ω_s`;
- the [rotor copper loss](rotor-copper-loss.md) is `s` times the air-gap power.
