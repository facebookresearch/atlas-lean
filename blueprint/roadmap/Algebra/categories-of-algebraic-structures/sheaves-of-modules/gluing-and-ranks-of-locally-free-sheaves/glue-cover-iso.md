# Gluing compatible local module isomorphisms

Let `F,G` be module sheaves over `(X,R)`, `U` an open cover, and `D : CoverIsoData F G U`
compatible local maps in both directions with the two pointwise inverse laws. Then
`glueCoverIso D hU : F ≅ G` has forward morphism determined by `glueCoverHom D.fwd hU` and
inverse morphism determined by `glueCoverHom D.bwd hU`.
