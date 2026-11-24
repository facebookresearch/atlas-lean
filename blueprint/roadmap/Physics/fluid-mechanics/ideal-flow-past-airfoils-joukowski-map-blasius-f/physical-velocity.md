# Physical-plane complex velocity through the far-field branch

For real `a`, `U`, `Γ`, `α` and complex `z`, let `ζ = ζ(z)` be the
[far-field branch](far-field-zeta.md) and `w` the [circle velocity](circle-velocity.md). The
physical complex velocity is `W(z) = w(ζ)/(1 − a²/ζ²)`, the circle velocity divided by the
derivative `1 − a²/ζ²` of the [Joukowski map](joukowski.md) at `ζ`.

Division uses the convention `x/0 = 0`. For `a ≠ 0` the denominator vanishes exactly when `ζ = ±a`;
for `a > 0` this happens exactly at `z = ±2a`, the ends of the plate, where `W(±2a) = 0` by the
convention. At `z = 0`, where `ζ(0) = 0`, `W(0) = U e^{−iα}`. For `a = 0`,
`W(z) = U e^{−iα} + Γ/(2πi z)`.

The intended domain is `a > 0` and `‖z‖ > 2a`, where `W` is holomorphic
([holomorphy](differentiable-on-physical-velocity.md)) and equals `U e^{−iα} + Γ/(2πi z)` up to a
remainder at most `K/‖z‖²` for `‖z‖ ≥ 4a` ([far-field bound](physical-velocity-far-field-bound.md)).
In the model, `W = u − iv` is the complex velocity of the flow past the plate from `−2a` to `2a`
that the Joukowski map carries over from the cylinder flow.
