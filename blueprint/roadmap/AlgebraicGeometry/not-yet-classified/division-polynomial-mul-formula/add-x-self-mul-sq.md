# Add X self mul Ψ₂Sq

The doubling formula: at a point `(x₁, y₁)` of `W` with
`y₁ ≠ negY x₁ y₁`, the `x`-coordinate of `(x₁, y₁) + (x₁, y₁)` times
`(Ψ₂Sq).eval x₁` is `(Φ 2).eval x₁`. This is Mathlib's
`Affine.addX_self_of_Y_ne` with the denominator cleared, stated with `Ψ₂Sq`
and `Φ 2`.
