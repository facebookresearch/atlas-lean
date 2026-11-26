# Product form via vanishing 2 × 2 minors

A complex array `M : Fin m → Fin n → ℂ` is in product form, meaning that
there are vectors `a : Fin m → ℂ` and `b : Fin n → ℂ` with `M i j = a i * b
j` for all `i` and `j`, if and only if all its `2 × 2` minors vanish: `M i₁
j₁ * M i₂ j₂ = M i₁ j₂ * M i₂ j₁` for all `i₁ i₂ j₁ j₂`.
