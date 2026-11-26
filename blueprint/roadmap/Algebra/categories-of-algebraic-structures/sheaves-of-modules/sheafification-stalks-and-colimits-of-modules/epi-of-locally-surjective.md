# Locally surjective module-sheaf morphisms are epimorphisms

Let `(D,K)` be a site and `S : Sheaf K RingCat.{u}`. For `g : A → B` between module sheaves of
carrier universe `u`, if every target section locally lifts through the underlying additive
presheaf morphism, then `g` is an epimorphism. The local-lifting hypothesis is
`Presheaf.IsLocallySurjective K ((PresheafOfModules.toPresheaf S.obj).map g.val)`.
