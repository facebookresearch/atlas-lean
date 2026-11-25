# Nodal data of a two-span beam from its span deflections

For lengths `L1`, `L2` and functions `y1`, `y2 : ℝ → ℝ` (the deflections of span 1 and span 2), the
global nodal data `(v0, θ0, v1, θ1, v2, θ2)` are
`(y1(0), y1'(0), y1(L1), y1'(L1), y2(L2), y2'(L2))`: span 1 gives nodes 0 and 1, span 2 gives
node 2. Derivatives are taken as `0` where the function is not differentiable.
