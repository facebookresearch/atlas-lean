# Action of a 3 × 3 matrix on a Voigt stiffness matrix

For a real `3 × 3` matrix `R` and a real `6 × 6` matrix `C`, the rotated Voigt matrix has entries

`C'_{IJ} = ∑_{a, b, c, d} R_{i a} R_{j b} R_{k c} R_{l d} C_{v(a, b) v(c, d)}`,

where `i` and `j` are the [first](voigt-fst.md) and [second](voigt-snd.md) axes of `I`, `k` and `l`
those of `J`, `v` is the [Voigt index](voigt-index.md) of a pair, and the sum runs over the axes
`a, b, c, d ∈ {x, y, z}`. This is the transformation
`c'_{ijkl} = ∑ R_{ia} R_{jb} R_{kc} R_{ld} c_{abcd}` of the rank-four tensor
`c_{abcd} = C_{v(a, b) v(c, d)}`, read back in Voigt form. Neumann invariance of a stiffness matrix
`C` under a point-group element `R` is `C' = C`, a modelling premise.
