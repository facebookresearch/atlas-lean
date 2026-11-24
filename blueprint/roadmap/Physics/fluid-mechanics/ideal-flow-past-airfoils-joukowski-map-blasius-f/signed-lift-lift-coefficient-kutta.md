# With a, ρ, U > 0, the Kutta lift coefficient is 2π sin α, near 2πα

Let `a > 0`, `ρ > 0`, `U > 0` and `R > 2a`, let `α` be real, and take the Kutta circulation
`Γ = −4πaU sin α` ([Kutta condition](kutta-cancellation.md)). Let `F` be the
[Blasius force](blasius-force.md), with density `ρ` and at radius `R`, of the
[physical complex velocity](physical-velocity.md) with this circulation and angle of attack `α`, and
`L` its [signed lift](signed-lift.md) at `α`. Then:

- `L = −ρUΓ = 4πρaU² sin α`;
- the [lift coefficient](lift-coefficient.md) with density `ρ`, speed `U` and chord
  `c = 4a` is `C_L = L/(ρU²(4a)/2) = 2π sin α`;
- `|C_L − 2πα| ≤ π|α|³/3` ([small-angle bound](abs-two-pi-sin-sub-two-pi-le.md)).

The force value comes from the
[Blasius force of the physical velocity](blasius-force-physical-velocity.md); the chord `4a` is the
length of the plate from `−2a` to `2a`. The lift here is the signed lift of the Blasius contour
force.
