# Torus boundary Word perm of perm

`L : List (Fin n × Fˣ)` encodes `word L = ∏ torus` via
`L.map (fun p => torus p.1.val n p.2) |>.prod`. If `L₁.Perm L₂` then
`word L₁ = c * word L₂` with `c ∈ torusCocycleSubgroup` left.
`cons` uses `torusCocycleSubgroup_le_center`; `swap` uses
`torus_last_mul_eq_cocycle_mul_swap`; `trans` multiplies defects.
