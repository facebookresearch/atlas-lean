# Angular momentum of a rigid body about its centre of mass

Let `M` be a rigid-body motion in three dimensions: a rigid body given by a mass distribution `ρ`
(a linear functional on smooth functions of the body point `y`, written `∫ f dm`) with centre of
mass `c = (1/m) ∫ y dm`, where `m = ∫ 1 dm` is the total mass (`c = 0` when `m = 0`), a
centre-of-mass trajectory `t ↦ X(t)` and an orientation `t ↦ R(t) ∈ SO(3)`. Its angular
momentum about the centre of mass at time `t` is `L_COM(t) = ∫ (x - X(t)) × (v - V(t)) dm`, where
`x = X(t) + R(t) (y - c)` is the position of the body point `y`, `v = Ṙ(t) (y - c) + V(t)` its
velocity and `V = Ẋ` the velocity of the centre of mass. Time derivatives are taken to be `0` where
the function is not differentiable; for a differentiable motion `v` is the velocity of the point.
