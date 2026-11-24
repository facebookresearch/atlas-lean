# The collapse load is the greatest admissible load intensity

For a span `L > 0` and a plastic moment `Mp ≥ 0`, `16 * Mp / L ^ 2` is the greatest load intensity
`w` for which a statically admissible moment field exists: a vector `σ` of moments at the three
critical sections satisfying the equilibrium equation `Bᵀ σ = w f`, that is
`(-2 σ₀ + 4 σ₁ - 2 σ₂) / L = w * L / 2`, with the [hinge-rotation matrix](hinge-rotation.md)
`B = (-2 / L, 4 / L, -2 / L)ᵀ` (a 3 × 1 matrix: rows the critical sections at the left end, mid-span
and right end; column the central deflection) and the [work vector](uniform-load-work.md)
`f = (L / 2)`, and `|σ_e| ≤ Mp` at each section. The upper bound is the weak-duality bound of the
finite plastic work certificate applied to the normalized mechanism. This is a statement about the
three-section model, not a collapse theorem for the continuous beam.
