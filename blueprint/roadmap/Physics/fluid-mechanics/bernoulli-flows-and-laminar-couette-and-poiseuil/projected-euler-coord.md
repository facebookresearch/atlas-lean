# Euler equations projected on the velocity in affine coordinates

Let `ρ > 0`, and let a flow of three-dimensional space have the constant density `ρ`, a steady
velocity `u` (`u(t, x)` independent of `t`) that is differentiable in `x` at every time, satisfy the
Euler equations in conservative form (continuity, Cauchy momentum balance and inviscid stress) with
a pressure `p`, and have a body force with the potential `Φ` (the specific body force is `-∇Φ`).
Then for every time `t₀`, origin `o` and coordinate point `v`, with the coordinate expressions
`u_E(w) = u(t₀, o + w)`, `p_E(w) = p(t₀, o + w)` and `Φ_E(w) = Φ(o + w)`,
`u_E(v) · (Du_E(v) u_E(v)) + (1 / ρ) Dp_E(v) u_E(v) + DΦ_E(v) u_E(v) = 0`: the momentum equation
projected on the velocity, the premise of the
[coordinate streamline Bernoulli theorem](../bernoulli-s-theorem-along-a-streamline/bernoulli-along-streamline.md).
