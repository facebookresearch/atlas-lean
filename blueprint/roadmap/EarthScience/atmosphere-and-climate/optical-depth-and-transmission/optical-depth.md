# Optical depth of an absorbing layer

The optical depth of an absorption-only layer from `a` to `b`, for an absorption coefficient
`κ : ℝ → ℝ`, is the interval integral `τ(a, b) = ∫ₐᵇ κ(x) dx`, for all real `a` and `b`; for
`b < a` it is minus the integral of `κ` over `[b, a]`. It is `0` when `κ` is not integrable on
the interval, the convention for the integral of a non-integrable function. In use, `a ≤ b` and
`κ` is nonnegative and integrable.
