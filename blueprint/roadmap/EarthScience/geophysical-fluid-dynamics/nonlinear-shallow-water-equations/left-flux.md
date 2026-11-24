# Left numerical flux

For a gravitational acceleration `g`, a numerical flux `𝓕` and the left and right cells
`(hL, uL, zL)` and `(hR, uR, zR)` of a face, the left numerical flux is the
[interface flux](interface-flux.md) plus the correction `(0, g hL² / 2 - g hL′² / 2)`, where
`hL′ = max(0, hL + zL - max(zL, zR))` is the left [reconstructed depth](face-depth.md) (source
(2.15)). The left cell uses it at its right face.
