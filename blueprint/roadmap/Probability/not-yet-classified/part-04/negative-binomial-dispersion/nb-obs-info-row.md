# Nb Obs Info Row

The observed information of one count `y` with covariate row `x` and linear predictor `η`,
i.e. minus the Hessian of `(β, θ) ↦ nbLogPmf θ y (x ⬝ᵥ β + o)`:
`[[w x xᵀ, -c x], [-c xᵀ, v]]` with `w = nbObsWeight θ y η`, `c = nbCross θ y η` and
`v = nbShapeObsInfo θ y η`.
