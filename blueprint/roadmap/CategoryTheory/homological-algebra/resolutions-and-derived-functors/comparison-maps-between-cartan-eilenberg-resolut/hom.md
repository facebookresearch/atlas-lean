# Hom

A supplied comparison of Cartan--Eilenberg resolutions over a chain map.

The four families are the boundary and homology endpoint lifts and the
strict horseshoe comparisons of the cycle and term rows.  In degree `j`
the cycle comparison has left endpoint `boundaryHom (j + 1)` and right
endpoint `homologyHom j`; the term comparison has left endpoint the cycle
comparison bundled as a morphism of cycle resolutions and right endpoint
`boundaryHom j`.  Lower-triangular coordinate formulas in Mathlib's
`Biprod.ofComponents` convention (vanishing left-endpoint-to-right-endpoint'
component, free right-endpoint-to-left-endpoint' cross component) are not
stored: they are derived by `Hom.cyclesHom_spec` and `Hom.termHom_spec`.
