# Skorokhod Space

The **Skorokhod space** `D([0, T], ℝ)`: real càdlàg paths on `[0, T]` (right-continuous
with left limits, Mathlib's `IsCadlag`). It carries the J1 extended pseudo-metric
`skorokhodEDist` and its Borel σ-algebra.

## Sources

- Billingsley (1999), §12 (space `D` with the Skorokhod J1 topology). Only the extended pseudo-metric axioms are proved here; separability, completeness of the Billingsley metric `d°`, and the identification of the Borel σ-algebra with the projection σ-algebra are not.
