# Velocity of the second body just after a two-body impact

For real `m₁`, `m₂`, `e`, `v₁` and `v₂`, the velocity of body 2 just after the impact is
`u₂ = (m₁ v₁ + m₂ v₂ + m₁ e (v₁ - v₂)) / (m₁ + m₂)`, with the same conventions as for
[body 1](impact-velocity.md). In the model the masses are positive and the coefficient of
restitution `e` lies in `[0, 1]`; the definition takes any real values. With the convention
`x / 0 = 0` the value is `0` when `m₁ + m₂ = 0`.
