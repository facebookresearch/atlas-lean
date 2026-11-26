# Epimorphisms under restriction along a base arrow

Let `(D,K)` be a site and `S : Sheaf K RingCat.{u}`. Assume additive sheafification and the
locally-bijective comparison on every `K.over X`. For `g : X → Y` and an epimorphism `f : M →
N` between module sheaves over `S.over Y`, the restricted morphism `(SheafOfModules.overMap S
g).map f` is an epimorphism over `S.over X`.
