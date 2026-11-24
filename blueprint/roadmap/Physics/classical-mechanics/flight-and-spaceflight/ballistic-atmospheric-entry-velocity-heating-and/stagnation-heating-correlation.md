# Stagnation Heating Correlation

A supplied stagnation-point heating correlation of the Sutton-Graves form
`q = kSG * sqrt (ρ / rn) * v ^ 3`: the convective heat flux per unit area at the stagnation point
of a blunt nose of radius `rn` moving at speed `v` through free-stream density `ρ`. The record
holds the citation (provenance only, not an applicability condition), the coefficient `kSG ≥ 0`
and the validity box `0 ≤ ρ ≤ ρmax`, `rmin ≤ rn`, `0 ≤ v ≤ vmax` with `rmin > 0`, which is
nonempty. Coefficient and box are calibration evidence supplied with the correlation; nothing
here asserts that the formula is physically adequate inside or outside the box.
