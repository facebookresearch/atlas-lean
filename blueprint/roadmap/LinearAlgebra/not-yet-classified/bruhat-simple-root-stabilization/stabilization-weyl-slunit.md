# Stabilization weyl SLUnit

Matrix endpoint: `SL` stabilization sends the simple-root Weyl element
at `(i,j)` to the Weyl element at `(castSucc i, castSucc j)`, preserving
`u` exactly. Uses `weylSLUnit_eq_monomialSLHom` and
`monomialSLHom_monomialSLSuccHom`; no matrix entry computation.
