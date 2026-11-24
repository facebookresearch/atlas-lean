# Trajectories obeying the network laws on a set of times

For a set `S` of times, a [trajectory](network-trajectory.md) obeys the laws of a
[network plant](network-plant.md) on `S` when, at every `t ∈ S`: `v(t) = Bᵀ φ(t)`; `B i(t) = j(t)`;
`v_e(t) = R_e i_e(t)` for `e ∈ R`; for `e ∈ C`, `v_e` is differentiable within `S` at `t` and
`i_e(t) = C_e v_e'(t)`; and for `e ∈ L`, `i_e` is differentiable within `S` at `t` and
`v_e(t) = L_e i_e'(t)`, the derivatives being taken within `S` (one-sided at an endpoint of an
interval, and taken to be `0` at an isolated point of `S`). The relation depends only on the values
of the signals at times of `S`.
