# The elastic moments at the collapse load are not admissible

For every real span `L` and every plastic moment `Mp > 0`, the elastic moments at the collapse load,
`σ = (-(4 * Mp / 3), 2 * Mp / 3, -(4 * Mp / 3))` (Neal, p. 23: `-W l / 12` at the ends and
`W l / 24` at mid-span, with `W l = 16 * Mp`), satisfy the equilibrium equation `Bᵀ σ = w f`, that
is `(-2 σ₀ + 4 σ₁ - 2 σ₂) / L = w * L / 2` with the [hinge-rotation matrix](hinge-rotation.md)
`B = (-2 / L, 4 / L, -2 / L)ᵀ` (a 3 × 1 matrix: rows the critical sections at the left end, mid-span
and right end; column the central deflection), the [work vector](uniform-load-work.md) `f = (L / 2)`
and `w = 16 * Mp / L ^ 2`, but not every `|σ_e| ≤ Mp`: they exceed the plastic moment at the ends,
so they are not a static certificate. At `L = 0` the convention `x / 0 = 0` makes `B`, the load
intensity `16 * Mp / L ^ 2` and both sides of the equilibrium equation `0`; the physical reading is
`L > 0`.
