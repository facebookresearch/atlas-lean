# The joint score

For `θ > 0`, the joint log-likelihood is differentiable at `(β, θ)` with
derivative `(v, s) ↦ ⟪v, Xᵀ s(β, θ)⟫ + s · ∑ᵢ nbShapeScore θ yᵢ ηᵢ`: the `β`-block is the
fixed-shape score vector `nbGradient`, the `θ`-block is `nbJointShapeScore`.
