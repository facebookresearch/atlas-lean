/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.FGProjectiveCat.ConeRing.AbsorptionNaturality

/-!
# Original coefficient-ring absorption clients

The clients read the actual return square through both original
projections, and retain the exact native scalar-composition route.
-/

public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits ModuleCat.RingHomScalarExtension

universe uR uS uT

namespace FGProjectiveCat.ConeRing.AbsorptionNaturalityTests

variable {R : Type uR} {S : Type uS} {T : Type uT} [Ring R] [Ring S] [Ring T]

/-- Successive actual coefficient maps preserve the same original first matrix. -/
theorem two_coefficient_maps (f : R →+* S) (g : S →+* T) :
    _root_.ConeRing.map g (_root_.ConeRing.map f (_root_.ConeRing.firstProjection R)) =
      _root_.ConeRing.firstProjection T := by
  rw [map_firstProjection, map_firstProjection]

/-- The original native tensor intertwiner retains the actual scalar-composition square. -/
theorem original_scalar_composition (f g : R →+* S) (c : S)
    (hc : Intertwines f g c) (k : S →+* T) :
    Functor.whiskerRight (ringScalarExtensionIntertwiner f g c hc) (ringScalarExtension k) ≫
        (ringScalarExtensionCompIso g k).hom =
      (ringScalarExtensionCompIso f k).hom ≫
        ringScalarExtensionIntertwiner (k.comp f) (k.comp g) (k c)
          (ModuleCat.RingHomScalarExtension.Intertwines.map hc k) :=
  ringScalarExtensionIntertwiner_pushforward f g c hc k

/-- The mapped return followed by the original first projection recovers original extraction. -/
theorem return_first_projection (f : R →+* S) (X : category R) :
    (coefficientFunctor f).map ((absorption R).inv.app X) ≫
        (sumNaturality f).hom.app X ≫
          (sumBicone S).fst.app ((coefficientFunctor f).obj X) =
      (coefficientFunctor f).map ((extract R).app X) := by
  rw [sumNaturality_fst_app, ← Functor.map_comp]
  have h := congrArg (fun η => η.app X) (absorption_fst R)
  simp only [NatTrans.comp_app] at h
  exact congrArg (fun v => (coefficientFunctor f).map v) h

/-- The mapped return followed by the original second projection recovers the same tail route. -/
theorem return_second_projection (f : R →+* S) (X : category R) :
    ((coefficientFunctor f).map ((absorption R).inv.app X) ≫
        (sumNaturality f).hom.app X) ≫
          (sumBicone S).snd.app ((coefficientFunctor f).obj X) =
      (infinityNaturality f).hom.app X ≫
        (tailInclusionMap S).app ((coefficientFunctor f).obj X) := by
  rw [← absorptionNaturality_return_app, Category.assoc]
  have h := congrArg (fun η => η.app ((coefficientFunctor f).obj X)) (absorption_snd S)
  simp only [NatTrans.comp_app] at h
  exact congrArg (fun v => (infinityNaturality f).hom.app X ≫ v) h

/-- The original comparison returns the exact original double-extension object. -/
theorem infinity_comparison_return (f : R →+* S) (X : category R) :
    (infinityNaturality f).hom.app X ≫ (infinityNaturality f).inv.app X =
      𝟙 ((coefficientFunctor f).obj ((infinityFunctor R).obj X)) :=
  (infinityNaturality f).hom_inv_id_app X

end FGProjectiveCat.ConeRing.AbsorptionNaturalityTests

end
