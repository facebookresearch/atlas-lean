# Cokernel projection after restriction along a base arrow

Let `(D,K)` be a site and `S : Sheaf K RingCat.{u}`, with additive sheafification and the
locally-bijective comparison on every slice. For `g : X → Y` and `φ : M → N` over `S.over Y`,
put `F=SheafOfModules.overMap S g`. The image `F(cokernel.π φ)` is a colimit cofork projection
for `F(φ)` and zero, with point `F(coker φ)`.
