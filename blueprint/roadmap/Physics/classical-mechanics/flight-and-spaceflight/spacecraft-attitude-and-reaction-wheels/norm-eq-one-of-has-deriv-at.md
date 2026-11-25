# Body-rate quaternion kinematics keep a unit quaternion unit

Let `q` be a quaternion-valued function of time and `ω_B` a function of time with values in
`ℝ³` such that `q'(t) = (1/2) q(t) (0, ω_B(t))` at every real time `t`, the body rate entering as
a [pure quaternion](pure-quat.md) multiplied on the right. If `|q(0)| = 1`, then `|q(t)| = 1` for
every real `t`, negative times included.
