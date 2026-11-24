# Interface flux

For a numerical flux `𝓕`, a function of a left and a right state `(mass, momentum) ∈ ℝ²`, and a face
between a left cell of depth `hL`, velocity `uL` and bed `zL` and a right cell `(hR, uR)` on bed
`zR`, the interface flux is `𝓕` evaluated at the two [reconstructed face states](face-state.md) with
the face bed `max(zL, zR)` (source (2.11)). Pairs are (mass, momentum) and fluxes are positive
towards increasing `x`. No property of `𝓕` is assumed.
