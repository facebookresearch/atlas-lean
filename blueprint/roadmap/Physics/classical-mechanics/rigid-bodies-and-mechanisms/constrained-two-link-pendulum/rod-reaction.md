# Rod-normal reaction forces with given multipliers

For real multipliers `c₁`, `c₂` and a configuration `p = (p₁, p₂)`, the rod reaction is the pair of
forces `(c₁ p₁ - c₂ (p₂ - p₁), c₂ (p₂ - p₁))` on the two masses: the first rod acts on the first
mass along `p₁`; the second rod acts on the second mass along `p₂ - p₁` and on the first mass with
the opposite force. It is `(c₁ ∇g₁ + c₂ ∇g₂) / 2`, where `∇g₁ = (2 p₁, 0)` and
`∇g₂ = (-2 (p₂ - p₁), 2 (p₂ - p₁))` are the gradients of the two rod constraints.

At a configuration with `‖p₁‖ = l₁ > 0` and `‖p₂ - p₁‖ = l₂ > 0`, a tension `T₁ > 0` in the first
rod corresponds to `c₁ = -T₁ / l₁`, and a tension `T₂ > 0` in the second rod to `c₂ = -T₂ / l₂`.
