# Zero-speed states lie outside the box, where the plant fails

Let `s` be a trajectory of states `(x, z, θ, q)`, and let a rigid motion, a gravity vector and a
time `t` be given. If the [flight speed](flight-speed.md) at the state `s(t)` is `0`, then `s(t)`
lies outside the [actuator box](actuator-box.md). And if `s(t)` lies outside the box, the
[six-degree-of-freedom plant](six-dof-plant.md) with the
[longitudinal maps](longitudinal-maps.md) fails at `t`, whatever the motion and the gravity: the
maps are never evaluated outside the box.
