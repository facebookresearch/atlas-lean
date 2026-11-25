# Assembled stiffness matrix of a two-span continuous beam

For flexural rigidities `EI1`, `EI2` and lengths `L1`, `L2` (real numbers), the assembled stiffness
of the two-span continuous beam in the coordinates `(v0, θ0, v1, θ1, v2, θ2)` is
`K_c = G₁ᵀ K(EI1, L1) G₁ + G₂ᵀ K(EI2, L2) G₂`, with the [beam stiffness matrix](beam-stiffness.md)
`K` of each span and the gathers `G₁` and `G₂` of the [first](span-one-gather.md) and
[second](span-two-gather.md) span, so that the middle-node deflection and slope are shared. A span
of length `0` contributes the zero matrix. The physical reading is `EI1, L1, EI2, L2 > 0`.
