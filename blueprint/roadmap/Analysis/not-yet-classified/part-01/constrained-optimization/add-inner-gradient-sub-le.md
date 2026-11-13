# Add inner gradient sub le

The supporting-plane inequality with the gradient (MF11.4b): in a real Hilbert space, if `f`
is convex on `s`, `x ∈ s`, `y ∈ s`, and `f` is differentiable at `x`, then
`f x + ⟪∇f x, y - x⟫ ≤ f y`. This is ATLAS's `ConvexOn.add_fderiv_sub_le`, since
`⟪∇f x, v⟫ = fderiv ℝ f x v`.
