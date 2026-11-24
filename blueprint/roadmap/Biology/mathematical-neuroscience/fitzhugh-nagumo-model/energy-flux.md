# Energy flux of the FitzHugh–Nagumo field

For real parameters `a`, `b`, `ε`, `I` and a state `(v, w)`, the energy flux is

`2 v (v - v³/3 - w + I) + (2 w / ε) · ε (v + a - b w)`,

the inner product of the gradient `(2 v, 2 w / ε)` of the [energy](energy.md) with the
[field](field.md). It is the derivative of the energy along trajectories
([derivative of the energy along a trajectory](has-deriv-at-energy.md)). Where it is negative at a
point of a level set `v² + w²/ε = R`, the field points strictly into the sublevel set
`v² + w²/ε ≤ R`. With the convention `x / 0 = 0` the second term is `0` at `ε = 0`, so the flux is
then `2 v (v - v³/3 - w + I)`.
