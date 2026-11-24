# Torus Cocycle Subgroup mem of conj

Side-agnostic induction transport via centrality.

If `h` is the normalized rotated product, `h ∈ torusCocycleSubgroup`,
and `h = w * g * w⁻¹` (exact noncommutative conjugacy with `w` the last
block), then `g ∈ torusCocycleSubgroup`. Uses
`torusCocycleSubgroup_le_center`: every element of the subgroup is central,
so conjugation is trivial on `h`, and `g = w⁻¹ * h * w = h`.

Orientation: agnostic to `inl`/`inr`; `w` may be any `StableSteinberg F`
element, in practice `lastBoundaryBlock n last`. Makes no length, chain,
or kernel claim beyond the two hypotheses.
