# Body torque of the saturated rate feedback

For a gain `k`, a limit `U_max` and a body rate `ω`, all real, the body torque of the rate
feedback is the [saturation](clip.md) of `−k ω` at `U_max`,

`τ_b(ω) = clip(−k ω) = max(−U_max, min(−k ω, U_max))`.

In the reduced fixed-axis wheel model it is the torque `−u_w` on the body with the wheel locked,
`u_w` the commanded rate of the wheel momentum. In the physical reading `k > 0` and `U_max > 0`;
for `U_max < 0` the value is `−U_max` at every rate.
