# For positive masses, the kinetic energy lost in a two-body impact

Let `m₁ > 0` and `m₂ > 0`. For all real `e`, `v₁` and `v₂`, with the post-impact velocities
`u₁ = (m₁ v₁ + m₂ v₂ - m₂ e (v₁ - v₂)) / (m₁ + m₂)` and
`u₂ = (m₁ v₁ + m₂ v₂ + m₁ e (v₁ - v₂)) / (m₁ + m₂)` ([first](impact-velocity.md) and
[second](impact-velocity-2.md) body), the [kinetic energy](pair-kinetic-energy.md)
`K(x₁, x₂) = m₁ x₁² / 2 + m₂ x₂² / 2` of the pair satisfies

`K(v₁, v₂) - K(u₁, u₂) = (1 - e²) m₁ m₂ / (2 (m₁ + m₂)) (v₁ - v₂)²`.

The identity holds for every real `e`; its sign depends on the range of `e`
([no gain for `0 ≤ e ≤ 1`](impact-energy-le.md),
[gain for `e > 1` and `v₁ ≠ v₂`](impact-energy-lt-of-one-lt.md)).

Equivalently, with no external force each body keeps its post-impact velocity on the
[constant-force trajectory](../../particles-and-oscillations/kinetic-energy-and-power-of-a-force/const-force-velocity.md)
with force `0`, so at every real time `t` after the event the kinetic energy of the pair is
`K(v₁, v₂)` minus the event loss `(1 - e²) m₁ m₂ / (2 (m₁ + m₂)) (v₁ - v₂)²`.
