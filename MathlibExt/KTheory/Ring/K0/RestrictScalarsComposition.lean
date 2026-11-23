/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.FGProjectiveCat.RestrictScalarsBaseChange
public import MathlibExt.Algebra.Category.FGProjectiveCat.BaseChangeRestrictScalarsDecomposition
public import MathlibExt.KTheory.Ring.K0.RestrictScalars

/-!
# The original K₀ composition for a two-coordinate coefficient extension

The actual module decomposition of restriction after scalar extension
gives multiplication by two on the entire original additive K₀ map.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped ChangeOfRings

universe u

namespace AlgebraicKTheory.RingK0

variable {R S : Type u} [CommRing R] [CommRing S]

/-- A finite projective extension with an actual pair of coefficient
coordinates doubles the whole original additive K₀ map. -/
theorem restrictScalars_comp_mapRingHom
    (f : R →+* S) (hf : f.IsFinite)
    (hp : @Module.Projective R _ S _ f.toModule)
    (eS : letI : Module R S := f.toModule; S ≃ₗ[R] R × R) :
    (restrictScalars f hf hp).comp (mapRingHom f).toAddMonoidHom =
      2 • AddMonoidHom.id (RingK0 R) := by
  apply K0.hom_ext
  intro P
  change restrictScalars f hf hp (mapRingHom f (K0.mk P)) = 2 • K0.mk P
  rw [mapRingHom_mk, restrictScalars_mk,
    K0.mk_congr_of_iso (FGProjectiveCat.restrictScalarsBaseChangeBiprodIso f hf hp eS P),
    K0.mk_biprod]
  exact (two_nsmul (K0.mk P)).symm

/-- An actual coefficient tensor splitting proves the whole original K₀
composition is identity plus the automorphism scalar-extension map. -/
theorem mapRingHom_comp_restrictScalars
    (f : R →+* S) (hf : f.IsFinite)
    (hp : @Module.Projective R _ S _ f.toModule) (σ : S ≃+* S)
    (hσ : σ.toRingHom.comp f = f)
    (e : (FGProjectiveCat.restrictScalars f hf hp ⋙ FGProjectiveCat.baseChange f).obj
      (FGProjectiveCat.regular S) ≃ₗ[S] S × S)
    (he : ∀ z w : S, e (z ⊗ₜ[R,f] w) = (z * w, z * σ w)) :
    (mapRingHom f).toAddMonoidHom.comp (restrictScalars f hf hp) =
      AddMonoidHom.id (RingK0 S) + (mapRingHom σ.toRingHom).toAddMonoidHom := by
  apply K0.hom_ext
  intro P
  change mapRingHom f (restrictScalars f hf hp (K0.mk P)) =
    K0.mk P + mapRingHom σ.toRingHom (K0.mk P)
  rw [restrictScalars_mk, mapRingHom_mk,
    K0.mk_congr_of_iso (FGProjectiveCat.baseChangeRestrictScalarsBiprodIso f hf hp σ hσ e he P),
    K0.mk_biprod, mapRingHom_mk]

end AlgebraicKTheory.RingK0

end
