# Torus eq torus Cocycle At mul swap

Central-defect torus transporter: `torus i j u` equals the central cocycle
defect `torusCocycleAt i j u (-1)` times the swapped torus `torus j i u⁻¹`.
Proved noncircularly from `weyl_swap`, `weyl_neg_eq_inv`, `torus`, and
`torus_mul_eq_torusCocycleAt_mul`; no defect-free equality
`torus i j u = torus j i u⁻¹` is claimed.
