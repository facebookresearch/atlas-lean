# Power Split of ne zero

Power split for any rotor current `I2`, at any nonzero slip and nonzero
synchronous speed, motoring or generating: the converted power is the
torque times the rotor speed `(1 - s) * ws` and the fraction `1 - s` of
the air-gap power, and the rotor copper loss is the fraction `s`. With
`s ≠ 0`, the copper term `3 ‖I2‖² R2` is `s` times the air-gap term
`3 ‖I2‖² (R2 / s)`, and the remaining difference is `1 - s` times that
air-gap term. The torque form then follows from `developedTorque`, using
`ws ≠ 0`.
