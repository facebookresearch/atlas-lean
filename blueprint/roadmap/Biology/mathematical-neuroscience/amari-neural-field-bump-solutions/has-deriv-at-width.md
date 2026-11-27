# Amari's interface equation

**Amari's interface equation** (Amari 1977). Let `w` be continuous, even and integrable and
`h, s ∈ ℝ`. Let `u : ℝ → ℝ → ℝ` be `C¹` in `(x, t)` and solve
`∂_t u(x, t) = -u(x, t) + fieldInput w h s (u · t) x` for all `x, t`. Let `x₁, x₂ : ℝ → ℝ` be
differentiable with `x₁ t < x₂ t` and `{x | h < u x t} = (x₁ t, x₂ t)` for all `t`, and let the
slopes `c₁ t = ∂_x u(x₁ t, t)` and `c₂ t = -∂_x u(x₂ t, t)` be positive for all `t`. Then for every
`t` the width `a = x₂ - x₁` has derivative `(W(a(t)) + s - h) (1 / c₁ t + 1 / c₂ t)` at `t`.

## Sources

- S. Amari, "Dynamics of pattern formation in lateral-inhibition type neural fields", Biol. Cybern. 27 (1977) 77–87.
