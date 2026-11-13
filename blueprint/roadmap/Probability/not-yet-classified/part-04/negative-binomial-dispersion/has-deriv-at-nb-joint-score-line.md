# The joint observed information is minus the Hessian

For `θ > 0` and a direction
`d = (u, s)`, the derivative at `t = 0` of `t ↦ ∇ℓ(p + t d) · d` (the joint score of
`hasFDerivAt_nbJointLogLik` applied to `d`) is `-dᵀ J d` with `J = nbJointObsInfo θ X o y β`.
