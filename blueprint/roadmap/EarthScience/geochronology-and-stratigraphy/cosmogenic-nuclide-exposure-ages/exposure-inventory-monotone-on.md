# Starting at or below saturation, the inventory never decreases

For a production rate `P > 0`, a decay constant `λ > 0` and an inherited inventory `N0` at or
below the saturation value, `N0 ≤ P / λ`, the inventory
`N(t) = N0 * exp (-λ * t) + (P / λ) * (1 - exp (-λ * t))` is monotone (nondecreasing) in `t` on
`t ≥ 0`.
