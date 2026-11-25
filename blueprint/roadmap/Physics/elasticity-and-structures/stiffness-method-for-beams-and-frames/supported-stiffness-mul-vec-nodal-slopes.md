# The exact nodal slopes solve the supported two-span beam system

Let `EI1, L1, EI2, L2 > 0`, and let `y1` and `y2` be quartic polynomials,
`y_i(x) = a_i + b_i x + c_i x² + d_i x³ + e_i x⁴` for all real `x`, with `EI_i y_i'''' = w_i` on
`[0, L_i]`. Suppose the spans are continuous at the middle node, `y1(L1) = y2(0)` and
`y1'(L1) = y2'(0)`, and simply supported, `y1(0) = 0`, `y1(L1) = 0` and `y2(L2) = 0`. Let
`F_i = (F_i1, F_i2, F_i3, F_i4)` be the [end forces](beam-end-forces.md) of `y_i` with `EI_i` and
`L_i`, and let `m = (F_12, F_14 + F_22, F_24)` collect their moment entries at the three nodes. Let
`p` be the [assembled load vector](continuous-beam-load-vector.md) of `w1` and `w2`.

Then the exact nodal slopes solve the supported finite-element system:
`K_s (y1'(0), y1'(L1), y2'(L2)) = Sᵀ p + m`, with the [supported stiffness](supported-stiffness.md)
`K_s` and the [support injection](support-injection.md) `S`.
