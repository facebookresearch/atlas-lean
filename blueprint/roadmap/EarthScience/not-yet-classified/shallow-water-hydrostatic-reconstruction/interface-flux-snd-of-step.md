# One-sided correction on a step

For a wet lake at rest over a
step whose left bed is lower, `zL < zR`, with `0 < g` and a numerical
flux consistent on wet states, the uncorrected interface momentum flux
equals the right (higher) cell's hydrostatic flux `g * hR ^ 2 / 2` and is
strictly below the left (lower) cell's `g * hL ^ 2 / 2`. With the face
balance, only the lower side's correction is nonzero; without it the
left cell would see a spurious momentum imbalance at this face.
