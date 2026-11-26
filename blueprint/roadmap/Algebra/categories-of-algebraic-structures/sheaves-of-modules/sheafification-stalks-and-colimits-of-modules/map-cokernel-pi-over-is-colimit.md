# Cokernel projection after restriction to a slice

Let `(D,K)` be a site and `S : Sheaf K RingCat.{u}`. Assume additive sheafification and the
locally-bijective comparison on `K` and all `K.over X`. For `φ : M → N` between module sheaves
of carrier universe `u` and `X∈D`, set `F=SheafOfModules.overFunctor S X`. The cofork with
point `F(coker φ)` and projection `F(cokernel.π φ)` is a colimit cofork of `F(φ)` and zero.
