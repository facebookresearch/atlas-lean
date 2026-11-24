# Static certificate at the collapse load

For every real span `L` and every plastic moment `Mp ≥ 0`, the moments `σ = (-Mp, Mp, -Mp)` at the
left end, mid-span and right end satisfy the equilibrium equation `Bᵀ σ = w f`, that is
`(-2 σ₀ + 4 σ₁ - 2 σ₂) / L = w * L / 2` with the [hinge-rotation matrix](hinge-rotation.md)
`B = (-2 / L, 4 / L, -2 / L)ᵀ` (a 3 × 1 matrix: rows the critical sections at the left end, mid-span
and right end; column the central deflection), the [work vector](uniform-load-work.md) `f = (L / 2)`
and the load intensity `w = 16 * Mp / L ^ 2`, and `|σ_e| ≤ Mp` at each of the three critical
sections (Neal, Fig. 2.5(d), Kazinczy's collapse load). At `L = 0` the convention `x / 0 = 0` makes
`B`, the load intensity `16 * Mp / L ^ 2` and both sides of the equilibrium equation `0`; the
physical reading is `L > 0`.
