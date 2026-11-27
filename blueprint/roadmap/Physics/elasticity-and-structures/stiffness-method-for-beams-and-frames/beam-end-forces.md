# End forces of a beam deflection field

For a flexural rigidity `EI`, a length `L` and a function `y : ℝ → ℝ`, the conjugate end-force
vector of `y`, in the nodal order `(v1, θ1, v2, θ2)`, is
`(EI y'''(0), -EI y''(0), -EI y'''(L), EI y''(L))`. With the bending moment `M = -EI y''` and the
shear force `V = M' = -EI y'''`, it is `(-V(0), M(0), V(L), -M(L))`. Derivatives are taken as `0`
where the function is not differentiable. The physical reading is `EI > 0` and `L > 0`.
