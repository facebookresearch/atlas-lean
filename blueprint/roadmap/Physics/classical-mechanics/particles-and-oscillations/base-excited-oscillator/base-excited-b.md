# Base Excited B

Input matrix `!![0, 0; 1 / m, -1]` for the input `(p, a_g)`: the applied force
`p` enters the velocity row with gain `1 / m`, the base acceleration `a_g` with
gain `-1`, and neither enters the displacement row. Meaningful for `m > 0`. The force
channel is the `OscillatorResponse.phaseForcing` channel on `ℝ × ℝ`.
