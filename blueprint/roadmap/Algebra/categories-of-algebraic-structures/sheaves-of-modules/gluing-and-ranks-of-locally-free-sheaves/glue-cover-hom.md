# Glued module-presheaf morphism from local cover data

Let `F,G` be module sheaves on `(X,R)`, `U` an open cover, and `D : CoverHomData F G U`. The
morphism `glueCoverHom D hU : F.val → G.val` has component at `V` the `R(V)`-linear map `s ↦
gluedApp D hU V s`. These components commute with restrictions, so the presheaf morphism
determines a module-sheaf morphism.
