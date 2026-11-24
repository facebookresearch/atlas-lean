# Converted Power eq torque mul rotor Speed

Converted power is torque times rotor speed `(1 - s) * ws`, for the
model current on the motoring interval. This is `powerSplit_of_ne_zero`
specialized to that current; it uses only `s ≠ 0` and `ws ≠ 0`, and keeps
the motoring hypotheses shared by the other results of this file.
