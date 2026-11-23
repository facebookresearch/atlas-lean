/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHClosedCellTransfinite

/-!
# Tests for injective transfinite colimits in CGWH
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace MathlibExtTest.CGWHClosedCellTransfiniteTests

#check CGWH.injective_map_of_injective_succ
#check CGWH.compactlyGeneratedColimit_isWeakHausdorff_of_injective_succ
#check CGWH.transfiniteColimitComparisonIso
#check CGWH.transfiniteColimitComparisonIso_hom_ι
#check CGWH.isColimitMapCoconeOfInjectiveSucc
#check CGWH.transfiniteColimit_ι_injective
#check CategoryTheory.TransfiniteCompositionOfShape.mapCgwhToCompactlyGeneratedOfInjective

section Generic

variable {J : Type v} [LinearOrder J] [OrderBot J] [SuccOrder J]
  [WellFoundedLT J]
variable (F : J ⥤ CGWH.{u, v}) [F.IsWellOrderContinuous]
variable (hSucc : ∀ (a : J) (_ha : ¬ IsMax a), Function.Injective
  (CGWH.cgwhToCompactlyGenerated.map
    (F.map (homOfLE (Order.le_succ a)))).hom)

example {a b : J} (f : a ⟶ b) : Function.Injective
    (CGWH.cgwhToCompactlyGenerated.map (F.map f)).hom :=
  CGWH.injective_map_of_injective_succ F hSucc f

example : UWeakHausdorffSpace.{u}
    ((Limits.colimit (F ⋙ CGWH.cgwhToCompactlyGenerated) :
      CompactlyGenerated.{u, v}) : Type v) :=
  CGWH.compactlyGeneratedColimit_isWeakHausdorff_of_injective_succ F hSucc

example : Limits.colimit (F ⋙ CGWH.cgwhToCompactlyGenerated) ≅
    CGWH.cgwhToCompactlyGenerated.obj (Limits.colimit F) :=
  CGWH.transfiniteColimitComparisonIso F hSucc

example (a : J) :
    Limits.colimit.ι (F ⋙ CGWH.cgwhToCompactlyGenerated) a ≫
        (CGWH.transfiniteColimitComparisonIso F hSucc).hom =
      CGWH.cgwhToCompactlyGenerated.map (Limits.colimit.ι F a) :=
  CGWH.transfiniteColimitComparisonIso_hom_ι F hSucc a

example (c : Cocone F) (hc : IsColimit c) :
    IsColimit (CGWH.cgwhToCompactlyGenerated.mapCocone c) :=
  CGWH.isColimitMapCoconeOfInjectiveSucc F hSucc c hc

example :
    (CGWH.transfiniteColimitComparisonIso F hSucc).hom ≫
        (CGWH.transfiniteColimitComparisonIso F hSucc).inv = 𝟙 _ := by
  simp

example :
    (CGWH.transfiniteColimitComparisonIso F hSucc).inv ≫
        (CGWH.transfiniteColimitComparisonIso F hSucc).hom = 𝟙 _ := by
  simp

example (a : J) : Function.Injective
    (CGWH.cgwhToCompactlyGenerated.map (Limits.colimit.ι F a)).hom :=
  CGWH.transfiniteColimit_ι_injective F hSucc a

variable {X Y : CGWH.{u, v}} {f : X ⟶ Y}
variable (c : CategoryTheory.TransfiniteCompositionOfShape J f)
variable (hcSucc : ∀ (a : J) (_ha : ¬ IsMax a), Function.Injective
  (CGWH.cgwhToCompactlyGenerated.map
    (c.F.map (homOfLE (Order.le_succ a)))).hom)

example : CategoryTheory.TransfiniteCompositionOfShape J
    (CGWH.cgwhToCompactlyGenerated.map f) :=
  c.mapCgwhToCompactlyGeneratedOfInjective hcSucc

example : CategoryTheory.Functor.IsWellOrderContinuous
    (c.mapCgwhToCompactlyGeneratedOfInjective hcSucc).F := inferInstance

example : IsColimit (Cocone.mk _
    (c.mapCgwhToCompactlyGeneratedOfInjective hcSucc).incl) :=
  (c.mapCgwhToCompactlyGeneratedOfInjective hcSucc).isColimit

example :
    (c.mapCgwhToCompactlyGeneratedOfInjective hcSucc).isoBot.inv ≫
        (c.mapCgwhToCompactlyGeneratedOfInjective hcSucc).incl.app ⊥ =
      CGWH.cgwhToCompactlyGenerated.map f :=
  (c.mapCgwhToCompactlyGeneratedOfInjective hcSucc).fac

end Generic

section BoundaryShapes

variable (F₁ : Fin 1 ⥤ CGWH.{u, 0})
variable (h₁ : ∀ (a : Fin 1) (_ha : ¬ IsMax a), Function.Injective
  (CGWH.cgwhToCompactlyGenerated.map
    (F₁.map (homOfLE (Order.le_succ a)))).hom)

example (a b : Fin 1) (f : a ⟶ b) : Function.Injective
    (CGWH.cgwhToCompactlyGenerated.map (F₁.map f)).hom :=
  CGWH.injective_map_of_injective_succ F₁ h₁ f

variable (F₂ : Fin 2 ⥤ CGWH.{u, 0})
variable (h₂ : ∀ (a : Fin 2) (_ha : ¬ IsMax a), Function.Injective
  (CGWH.cgwhToCompactlyGenerated.map
    (F₂.map (homOfLE (Order.le_succ a)))).hom)

example (a b : Fin 2) (f : a ⟶ b) : Function.Injective
    (CGWH.cgwhToCompactlyGenerated.map (F₂.map f)).hom :=
  CGWH.injective_map_of_injective_succ F₂ h₂ f

variable (Fₙ : ℕ ⥤ CGWH.{u, 0})
variable (hₙ : ∀ (a : ℕ) (_ha : ¬ IsMax a), Function.Injective
  (CGWH.cgwhToCompactlyGenerated.map
    (Fₙ.map (homOfLE (Order.le_succ a)))).hom)

example (a b : ℕ) (f : a ⟶ b) : Function.Injective
    (CGWH.cgwhToCompactlyGenerated.map (Fₙ.map f)).hom :=
  CGWH.injective_map_of_injective_succ Fₙ hₙ f

variable (Finfty : WithTop ℕ ⥤ CGWH.{u, 0}) [Finfty.IsWellOrderContinuous]
variable (hinfty : ∀ (a : WithTop ℕ) (_ha : ¬ IsMax a), Function.Injective
  (CGWH.cgwhToCompactlyGenerated.map
    (Finfty.map (homOfLE (Order.le_succ a)))).hom)

example : Function.Injective
    (CGWH.cgwhToCompactlyGenerated.map
      (Finfty.map (homOfLE (bot_le : (⊥ : WithTop ℕ) ≤ ⊤)))).hom :=
  CGWH.injective_map_of_injective_succ Finfty hinfty _

end BoundaryShapes

section UniverseCorners

#check CGWH.injective_map_of_injective_succ.{0, 0}
#check CGWH.injective_map_of_injective_succ.{1, 1}
#check CGWH.injective_map_of_injective_succ.{0, 1}
#check CGWH.injective_map_of_injective_succ.{1, 0}
#check CGWH.transfiniteColimitComparisonIso.{1, 0}
#check CGWH.isColimitMapCoconeOfInjectiveSucc.{0, 0}
#check CGWH.isColimitMapCoconeOfInjectiveSucc.{1, 1}
#check CGWH.isColimitMapCoconeOfInjectiveSucc.{0, 1}
#check CGWH.isColimitMapCoconeOfInjectiveSucc.{1, 0}
#check CategoryTheory.TransfiniteCompositionOfShape.mapCgwhToCompactlyGeneratedOfInjective.{0, 1}

end UniverseCorners

/- The provider installs no global coherence or colimit-preservation data. -/

#guard_msgs (error, substring := true) in
#synth BraidedCategory CompactlyGenerated.{0, 0}

#guard_msgs (error, substring := true) in
#synth PreservesColimitsOfSize.{0, 0} CGWH.cgwhToCompactlyGenerated.{0, 0}

/- The four proof helpers stay private. -/

open CGWH

/-- error: Unknown identifier `compactlyGeneratedColimit_isWeakHausdorff_of_injective` -/
#guard_msgs (error) in
#check compactlyGeneratedColimit_isWeakHausdorff_of_injective

/-- error: Unknown identifier `colimitComparisonToCompactlyGeneratedIso_of_weakHausdorff` -/
#guard_msgs (error) in
#check colimitComparisonToCompactlyGeneratedIso_of_weakHausdorff

/-- error: Unknown identifier `colimitComparisonToCompactlyGeneratedIso_of_weakHausdorff_hom_ι` -/
#guard_msgs (error) in
#check colimitComparisonToCompactlyGeneratedIso_of_weakHausdorff_hom_ι

/-- error: Unknown identifier `isColimit_mapCocone_cgwhToCompactlyGenerated_of_weakHausdorff` -/
#guard_msgs (error) in
#check isColimit_mapCocone_cgwhToCompactlyGenerated_of_weakHausdorff

#print axioms CGWH.injective_map_of_injective_succ
#print axioms CGWH.compactlyGeneratedColimit_isWeakHausdorff_of_injective_succ
#print axioms CGWH.transfiniteColimitComparisonIso
#print axioms CGWH.transfiniteColimitComparisonIso_hom_ι
#print axioms CGWH.isColimitMapCoconeOfInjectiveSucc
#print axioms CGWH.transfiniteColimit_ι_injective
#print axioms CategoryTheory.TransfiniteCompositionOfShape.mapCgwhToCompactlyGeneratedOfInjective

end MathlibExtTest.CGWHClosedCellTransfiniteTests
