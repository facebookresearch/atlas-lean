/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.FGProjectiveCat.BaseChangeRestrictScalarsDecomposition

noncomputable section

open CategoryTheory
open scoped ChangeOfRings

universe u

variable {R S : Type u} [CommRing R] [CommRing S]

example (f : R →+* S) (hf : f.IsFinite)
    (hp : @Module.Projective R _ S _ f.toModule) (P : FGProjectiveCat.{u} S) (p : P) :
    (FGProjectiveCat.baseChangeRestrictScalarsCounit f hf hp).app P
      ((1 : S) ⊗ₜ[R,f] p) = p :=
  FGProjectiveCat.baseChangeRestrictScalarsCounit_unit f hf hp P p

example (σ : S ≃+* S) (p : S) :
    (FGProjectiveCat.baseChangeAutomorphismRegularIso σ).hom
        (show (FGProjectiveCat.baseChange σ.toRingHom).obj (FGProjectiveCat.regular S) from
          (ModuleCat.extendRestrictScalarsAdj σ.toRingHom).unit.app (ModuleCat.of S S) p) =
      σ p :=
  FGProjectiveCat.baseChangeAutomorphismRegularIso_unit σ p

example (f : R →+* S) (hf : f.IsFinite)
    (hp : @Module.Projective R _ S _ f.toModule) (σ : S ≃+* S)
    (hσ : σ.toRingHom.comp f = f)
    (e : (FGProjectiveCat.restrictScalars f hf hp ⋙ FGProjectiveCat.baseChange f).obj
      (FGProjectiveCat.regular S) ≃ₗ[S] S × S)
    (he : ∀ z w : S, e (z ⊗ₜ[R,f] w) = (z * w, z * σ w)) :
    (FGProjectiveCat.baseChangeRestrictScalarsDecompositionIso f hf hp σ hσ e he).hom =
      FGProjectiveCat.baseChangeRestrictScalarsDecompositionMap f hf hp σ hσ := by simp

/-- The whole earned isomorphism includes the original empty finite-free rank. -/
example (f : R →+* S) (hf : f.IsFinite)
    (hp : @Module.Projective R _ S _ f.toModule) (σ : S ≃+* S)
    (hσ : σ.toRingHom.comp f = f)
    (e : (FGProjectiveCat.restrictScalars f hf hp ⋙ FGProjectiveCat.baseChange f).obj
      (FGProjectiveCat.regular S) ≃ₗ[S] S × S)
    (he : ∀ z w : S, e (z ⊗ₜ[R,f] w) = (z * w, z * σ w)) :
    (FGProjectiveCat.baseChange f).obj
        ((FGProjectiveCat.restrictScalars f hf hp).obj (FGProjectiveCat.standardFree S 0)) ≅
      FGProjectiveCat.standardFree S 0 ⊞
        (FGProjectiveCat.baseChange σ.toRingHom).obj (FGProjectiveCat.standardFree S 0) :=
  FGProjectiveCat.baseChangeRestrictScalarsBiprodIso f hf hp σ hσ e he _

end
