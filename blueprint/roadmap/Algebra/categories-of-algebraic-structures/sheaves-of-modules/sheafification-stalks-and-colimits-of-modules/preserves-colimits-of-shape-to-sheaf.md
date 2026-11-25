# Sheafification, stalks, and colimits of modules

The forgetful functor from sheaves of modules to abelian sheaves preserves
colimits of shape `K`.

Given `F : K ⥤ SheafOfModules R`, write `F₀ := F ⋙ forget` for the underlying
presheaf-module diagram and `c₀` for its colimit cocone. Module sheafification
`S` (a left adjoint) sends `c₀` to a colimit cocone, which the counit
isomorphism `e : F ≅ F₀ ⋙ S` transports to a colimit cocone on `F`. On the
abelian side, `T := toPresheaf` and `P := presheafToSheaf` (both
colimit-preserving) send `c₀` to a colimit cocone, transported along the
diagram iso `n` (built from `e` and `sheafificationCompToSheaf`) to a colimit
cocone on `F ⋙ toSheaf`. The two cocones on `F ⋙ toSheaf` agree by naturality
of `sheafificationCompToSheaf`, so the image cocone is a colimit.
