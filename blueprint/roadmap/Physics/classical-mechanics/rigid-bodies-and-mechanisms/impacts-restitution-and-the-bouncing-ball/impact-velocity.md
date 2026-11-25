# Velocity of the first body just after a two-body impact

For real `m₁`, `m₂`, `e`, `v₁` and `v₂`, the velocity of body 1 just after the impact is
`u₁ = (m₁ v₁ + m₂ v₂ - m₂ e (v₁ - v₂)) / (m₁ + m₂)`, where `v₁`, `v₂` are the velocities of the two
bodies just before it, components along the line of the impact, and `e` is the coefficient of
restitution. In the model the masses are positive and the coefficient of restitution `e` lies in
`[0, 1]`; the definition takes any real values. With the convention `x / 0 = 0` the value is `0`
when `m₁ + m₂ = 0`.
