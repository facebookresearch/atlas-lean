# Engineering-strain transformation to material axes

For a real angle `θ`, with `c = cos θ` and `s = sin θ`, the matrix

`T_e(θ) = [[c², s², c s], [s², c², −c s], [−2 c s, 2 c s, c² − s²]]`.

It maps the global engineering strains `(ε_xx, ε_yy, γ_xy)` to the engineering strains
`(ε₁₁, ε₂₂, γ₁₂)` in material axes at the angle `θ` from the global axes
([rotation of the strain](strain-map-mul-vec-strain-voigt.md)).
