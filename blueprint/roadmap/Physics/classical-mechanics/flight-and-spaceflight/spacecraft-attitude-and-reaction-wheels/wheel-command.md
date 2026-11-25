# Wheel command taking the reaction of the body torque

For real numbers `k`, `U_max` and `ω`, the wheel command is minus the
[body torque](body-torque.md) of the saturated rate feedback,

`u_w(ω) = −τ_b(ω) = −max(−U_max, min(−k ω, U_max))`:

the commanded rate of the wheel momentum, which takes the reaction of the body torque. In the
physical reading `k > 0` and `U_max > 0`; for `U_max < 0` the command is `U_max` at every rate.
