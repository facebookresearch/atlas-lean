# Right numerical flux

For a gravitational acceleration `g`, a numerical flux `𝓕` and the left and right cells
`(hL, uL, zL)` and `(hR, uR, zR)` of a face, the right numerical flux is the
[interface flux](interface-flux.md) plus the correction `(0, g hR² / 2 - g hR′² / 2)`, where
`hR′ = max(0, hR + zR - max(zL, zR))` is the right [reconstructed depth](face-depth.md) (source
(2.16)). The right cell uses it at its left face.
