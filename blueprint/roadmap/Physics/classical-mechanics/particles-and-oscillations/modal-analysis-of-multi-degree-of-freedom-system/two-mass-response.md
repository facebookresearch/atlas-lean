# Two-mass free response: centre-of-mass drift plus extension response

For real numbers `m₁`, `m₂` and `k`, initial positions `x₀ = (x₀₁, x₀₂)` and velocities
`v₀ = (v₀₁, v₀₂)`, and a time `t`, the two-mass response is

`x(t) = X(t) (1, 1) + (r(t) / (m₁ + m₂)) (-m₂, m₁)`,

where:

- `X(t) = X₀ + V₀ t` is the rigid drift of the centre of mass, with
  `X₀ = (m₁ x₀₁ + m₂ x₀₂) / (m₁ + m₂)` and `V₀ = (m₁ v₀₁ + m₂ v₀₂) / (m₁ + m₂)`;
- `r(t)` is the [modal response](modal-coordinate.md) for the
  [squared frequency](two-mass-frequency-sq.md) `ω² = k (m₁ + m₂) / (m₁ m₂)` starting from the
  spring extension `x₀₂ - x₀₁` with rate `v₀₂ - v₀₁`.

For `m₁, m₂ > 0` the extension oscillates at the angular frequency `√(ω²)` when `k > 0`; when
`k ≤ 0`, `ω² ≤ 0` and its response is the drift `(x₀₂ - x₀₁) + (v₀₂ - v₀₁) t`, so for `k = 0`, two
free masses, both terms drift. In the physical reading `m₁, m₂ > 0` and `k ≥ 0`; the formula uses
the convention `u / 0 = 0`.
