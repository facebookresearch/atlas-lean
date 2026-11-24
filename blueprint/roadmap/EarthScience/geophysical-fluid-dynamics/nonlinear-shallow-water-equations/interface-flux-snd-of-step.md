# One-sided correction on a step

Let `g > 0`, let the numerical flux `𝓕` be consistent on wet states:
`𝓕((h, h u), (h, h u)) = (h u, h u² + g h² / 2)` for every depth `h > 0` and velocity `u`, and let
the cells of a face be a lake at rest with free surface `η`: `hL + zL = η`, `hR + zR = η`,
`max(zL, zR) < η` (both cells strictly wet) and zero discharges `hL uL = 0`, `hR uR = 0`, over a
step with the lower bed on the left, `zL < zR`. Then the momentum component of the
[interface flux](interface-flux.md) equals the right (higher) cell's hydrostatic flux `g hR² / 2`
and is strictly below the left (lower) cell's `g hL² / 2`. So only the lower side's correction is
nonzero; without it the left cell would see a spurious momentum imbalance at this face.
