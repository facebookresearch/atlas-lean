# Holley inequality for increasing events

The **Holley inequality** for increasing events (Holley 1974). If `μ₁, μ₂ ≥ 0` have equal
total mass and satisfy `μ₁ a * μ₂ b ≤ μ₁ (a ⊓ b) * μ₂ (a ⊔ b)`, then `μ₁(A) ≤ μ₂(A)` for every
increasing event `A`. This is Mathlib's `holley` applied to the indicator of `A`.
