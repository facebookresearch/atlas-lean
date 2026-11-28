# A rigid rotation about the left end is in the two-span beam kernel

For all real `EI1`, `L1`, `EI2` and `L2`, the
[assembled two-span stiffness](continuous-beam-stiffness.md) `K_c` (without supports) maps the rigid
rotation about the left end, `r = (0, 1, L1, 1, L1 + L2, 1)`, to zero, `K_c r = 0`; this mode has
zero left deflection, and `r ≠ 0`. With only the left deflection supported it is therefore a
mechanism: one support is not enough. The physical reading is `EI1, L1, EI2, L2 > 0`.
