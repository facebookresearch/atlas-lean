# Restriction along a base arrow preserves cokernels

Let `(D,K)` be a site and `S : Sheaf K RingCat.{u}`. Assume additive sheafification and the
locally-bijective comparison on every slice `K.over X`. For `g : X → Y` and `φ : M → N`
between module sheaves over `S.over Y`, the functor `SheafOfModules.overMap S g` preserves the
colimit of `parallelPair φ 0`, hence the cokernel of `φ`.
