# For positive lengths each kernel vector has a unique angular velocity

Let `l₁ > 0` and `l₂ > 0`, `q` a pair of angles, and `v` a pair of plane vectors in the kernel of
the [rod constraint Jacobian](rod-jacobian.md) at the configuration given by the
[angle-to-position map](pos-map.md) at `q`. Then there is exactly one angular velocity `w` such that
the curve `s ↦ (p₁, p₂)(q + s w)` has derivative `v` at `s = 0`.
