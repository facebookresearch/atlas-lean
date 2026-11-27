# Quarter-turn examples of passive and active component maps

For the [quarter turn](quarter-turn-z.md) `R` about the third axis, with `e₁, e₂, e₃` the standard
basis of `ℝ³`:

- the [inertial components](body-to-inertial-vec.md) of `e₁` and `e₂` are `R e₁ = e₂` and
  `R e₂ = -e₁`;
- the moment `e₁ × e₂ = e₃` has inertial components `R (e₁ × e₂) = e₃`, which is also
  `(R e₁) × (R e₂)`;
- the [active rotation](rotate-active.md) turns `e₁` to `e₂`, while the
  [body components](inertial-to-body-vec.md) of `e₁` are `Rᵀ e₁ = -e₂`: the passive map to body
  components turns the other way.
