# Supported stiffness matrix of a two-span continuous beam

For real `EI1`, `L1`, `EI2` and `L2`, the supported stiffness on the free rotations is the 3 × 3
matrix `K_s = Sᵀ K_c S`, with the [assembled two-span stiffness](continuous-beam-stiffness.md) `K_c`
and the [support injection](support-injection.md) `S`. A span of length `0` contributes the zero
matrix, by the convention `x / 0 = 0`. The physical reading is `EI1, L1, EI2, L2 > 0`.
