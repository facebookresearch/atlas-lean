# Kinetic energy of a rigid body turning about a body axis

Let `M` be a rigid-body motion in three dimensions: a rigid body with a mass distribution, a
centre-of-mass trajectory and an orientation `t ↦ R(t) ∈ SO(3)`. Suppose its mass `m` is positive
and its body frame is centred at the centre of mass (the centre of mass of the body is the origin
of body coordinates), and let `t` be a time at which `R` is differentiable and the body angular
velocity is `(0, 0, ω)`, a rotation about the third body axis. Then the kinetic energy
`(1/2) ∫ ‖v‖² dm` of `M` at `t`, where `v = Ṙ(t) y + V(t)` is the velocity of the body point `y`, is

`T = m ‖V(t)‖² / 2 + J ω² / 2`,

where `V(t)` is the velocity of the centre of mass (taken to be `0` where the centre-of-mass
trajectory is not differentiable) and `J` is the diagonal entry of the inertia tensor about the
centre of mass for the third axis.
