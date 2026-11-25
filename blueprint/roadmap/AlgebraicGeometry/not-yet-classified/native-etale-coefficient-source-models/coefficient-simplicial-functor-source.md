# Coefficient Simplicial Functor Source

A functor from cochain complexes of sheaves of $\Lambda$-modules on the small étale site of $X$
($\Lambda$ a ring) to the simplicial category `sourceSimplicialCategory` obtained from their cochain
DG enrichment $N$ through the Dold–Kan correspondence, with prescribed values: through the given
equalities of objects, it sends each complex $F$ to `sourceObject F` and each cochain map $f$ to
`sourceMorphism f`, the vertex given by $f$ through the lax unit and the Dold–Kan map.
