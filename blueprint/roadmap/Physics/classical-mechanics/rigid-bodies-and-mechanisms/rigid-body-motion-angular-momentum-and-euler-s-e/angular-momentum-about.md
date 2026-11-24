# Angular momentum of a rigid body about a fixed point

Let `M` be a rigid-body motion in three dimensions, given as for the
[angular momentum about the centre of mass](com-angular-momentum.md) by a mass distribution
written `∫ f dm`, a centre of mass `c = (1/m) ∫ y dm` with total mass `m = ∫ 1 dm` (`c = 0` when
`m = 0`), a centre-of-mass trajectory `X` and an orientation `R`, and
let `O ∈ ℝ³` be a fixed point of the inertial frame. The angular momentum about `O` at time `t` is
`L_O(t) = ∫ (x - O) × v dm`, with `x = X(t) + R(t) (y - c)` and `v = Ṙ(t) (y - c) + Ẋ(t)` the
position and velocity of the body point `y` (time derivatives taken to be `0` where the function is
not differentiable).
