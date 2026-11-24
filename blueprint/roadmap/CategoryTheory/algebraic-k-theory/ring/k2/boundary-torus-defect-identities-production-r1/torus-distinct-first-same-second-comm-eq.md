# Torus distinct First same Second comm eq inv

Distinct-first same-second boundary commutator equality:
`⁅torus i n u, torus j n v⁆ = (torusCocycleAt n j v⁻¹ u⁻¹)⁻¹`.
Rewrites each boundary torus via `torus_eq_torusCocycleAt_mul_swap`, removes
the central left factors with `torusCocycleAt_mem_center`, then reuses
`torus_sameFirst_distinctSecond_comm_eq_inv` at `n` with units `u⁻¹, v⁻¹`.
