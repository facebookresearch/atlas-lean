# Wet-bed reconstructed face balance

Let `g` be real, let the numerical flux `𝓕` be consistent on wet states:
`𝓕((h, h u), (h, h u)) = (h u, h u² + g h² / 2)` for every depth `h > 0` and velocity `u`, and let
the cells of a face be a lake at rest with free surface `η`: `hL + zL = η`, `hR + zR = η`,
`max(zL, zR) < η` (both cells strictly wet) and zero discharges `hL uL = 0`, `hR uR = 0`. Then the
momentum component of the [left numerical flux](left-flux.md) is `g hL² / 2` and that of the
[right numerical flux](right-flux.md) is `g hR² / 2`: each corrected momentum flux equals the
hydrostatic momentum flux of the cell on its side. This is the momentum part of the source's Theorem
2.1 (ii), on the strictly wet domain only; the identities hold for every real `g`, and physically
`g > 0`.
