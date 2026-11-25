/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Presentable.Completeness
public import Mathlib.CategoryTheory.Presentable.Type
public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.CategoryTheory.SingleObj

/-!
# Entire original completeness and cofree contracts

No coefficient limit/product hypothesis is supplied. The independent
universe contracts check the original created functor, both comparison
directions, universal lifts and actual original Hom-indexed cofree maps.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe w uM vM uJ vJ uD vD

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Presentable.CompletenessTest

variable (M : Type uM) [Category.{vM} M] (κ : Cardinal.{w}) [Fact κ.IsRegular]
  [IsCardinalLocallyPresentable M κ]

example : HasLimitsOfSize.{w, w} M := Completeness.hasLimitsOfSize M κ

section OriginalShapes

variable (J : Type uJ) [Category.{vJ} J] [EssentiallySmall.{w} J]

example : HasLimitsOfShape J M := Completeness.hasLimitsOfShape M κ J

example (F : J ⥤ M) : IsLimit (Completeness.cone M κ J F) :=
  Completeness.isLimit M κ J F

example (F : J ⥤ M) (j : J) :
    (Completeness.comparison M κ J).hom.app F ≫ (Completeness.targetCones M κ J F).π.app j =
      (DenseReflectivePresentation.restrictedYoneda M κ).map
        ((Completeness.cone M κ J F).π.app j) :=
  Completeness.comparison_hom_π M κ J F j

example (F : J ⥤ M) (j : J) :
    (Completeness.comparison M κ J).inv.app F ≫
        (DenseReflectivePresentation.restrictedYoneda M κ).map
          ((Completeness.cone M κ J F).π.app j) =
      (Completeness.targetCones M κ J F).π.app j :=
  Completeness.comparison_inv_π M κ J F j

example (F : J ⥤ M) :
    (Completeness.limitFunctor M κ J).map (𝟙 F) = 𝟙 _ :=
  (Completeness.limitFunctor M κ J).map_id F

example {F G H : J ⥤ M} (α : F ⟶ G) (β : G ⟶ H) :
    (Completeness.limitFunctor M κ J).map (α ≫ β) =
      (Completeness.limitFunctor M κ J).map α ≫
        (Completeness.limitFunctor M κ J).map β :=
  (Completeness.limitFunctor M κ J).map_comp α β

example {F G : J ⥤ M} (α : F ⟶ G) (j : J) :
    (Completeness.limitFunctor M κ J).map α ≫ (Completeness.cone M κ J G).π.app j =
      (Completeness.cone M κ J F).π.app j ≫ α.app j :=
  Completeness.map_π M κ J α j

example {F G : J ⥤ M} (α : F ⟶ G) :
    (DenseReflectivePresentation.restrictedYoneda M κ).map
        ((Completeness.limitFunctor M κ J).map α) ≫
        (Completeness.comparison M κ J).hom.app G =
      (Completeness.comparison M κ J).hom.app F ≫
        (Completeness.targetLimitFunctor M κ J).map α :=
  (Completeness.comparison M κ J).hom.naturality α

example (F : J ⥤ M) (s : Cone F) (j : J) :
    Completeness.lift M κ J F s ≫ (Completeness.cone M κ J F).π.app j = s.π.app j :=
  Completeness.lift_π M κ J F s j

example (F : J ⥤ M) (s : Cone F) (m : s.pt ⟶ (Completeness.limitFunctor M κ J).obj F)
    (hm : ∀ j, m ≫ (Completeness.cone M κ J F).π.app j = s.π.app j) :
    m = Completeness.lift M κ J F s :=
  Completeness.lift_unique M κ J F s m hm

end OriginalShapes

section OriginalHomProducts

variable {D : Type uD} [Category.{vD} D] {S : Type w} [SmallCategory S] (s : D ≌ S)

example (d e : D) : HasProductsOfShape (d ⟶ e) M := Completeness.homProducts M κ s d e

example (d e : D) (X : M) :
    let _ : HasProductsOfShape (e ⟶ d) M := Completeness.homProducts M κ s e d
    ((Completeness.cofree M κ s d).obj X).obj e = ∏ᶜ fun _ : e ⟶ d ↦ X :=
  Completeness.cofree_obj M κ s d e X

example (d : D) {e e' : D} (a : e ⟶ e') (X : M) (g : e' ⟶ d) :
    let _ : HasProductsOfShape (e ⟶ d) M := Completeness.homProducts M κ s e d
    let _ : HasProductsOfShape (e' ⟶ d) M := Completeness.homProducts M κ s e' d
    ((Completeness.cofree M κ s d).obj X).map a ≫ Pi.π (fun _ : e' ⟶ d ↦ X) g =
      Pi.π (fun _ : e ⟶ d ↦ X) (a ≫ g) :=
  Completeness.cofree_map_π M κ s d a X g

example (d e : D) {X Y : M} (f : X ⟶ Y) (g : e ⟶ d) :
    let _ : HasProductsOfShape (e ⟶ d) M := Completeness.homProducts M κ s e d
    ((Completeness.cofree M κ s d).map f).app e ≫ Pi.π (fun _ : e ⟶ d ↦ Y) g =
      Pi.π (fun _ : e ⟶ d ↦ X) g ≫ f :=
  Completeness.cofree_coefficient_map_π M κ s d e f g

example (d e : D) (F : D ⥤ M) (X : M) (f : F.obj d ⟶ X) :
    let _ : HasProductsOfShape (e ⟶ d) M := Completeness.homProducts M κ s e d
    (((Completeness.evaluationCofreeAdjunction M κ s d).homEquiv F X) f).app e =
      Pi.lift (fun g : e ⟶ d ↦ F.map g ≫ f) :=
  Completeness.cofree_homEquiv_app M κ s d e F X f

example (d : D) (F : D ⥤ M) (X : M) :
    let _ : HasProductsOfShape (d ⟶ d) M := Completeness.homProducts M κ s d d
    (((Completeness.evaluationCofreeAdjunction M κ s d).homEquiv F X).symm :
      (F ⟶ (Completeness.cofree M κ s d).obj X) → (F.obj d ⟶ X)) =
      fun α ↦ α.app d ≫ Pi.π (fun _ : d ⟶ d ↦ X) (𝟙 d) := by
  funext α
  exact Completeness.cofree_homEquiv_symm M κ s d F X α

example (d e : D) (X : M) :
    let _ : HasProductsOfShape (e ⟶ d) M := Completeness.homProducts M κ s e d
    (Completeness.homPower M κ s d e).obj X = ∏ᶜ fun _ : e ⟶ d ↦ X :=
  Completeness.homPower_obj M κ s d e X

end OriginalHomProducts

section Concrete

attribute [local instance] Cardinal.fact_isRegular_aleph0

example : HasLimitsOfSize.{0, 0} (Type) := Completeness.hasLimitsOfSize (Type) Cardinal.aleph0.{0}

example : HasLimitsOfShape (Discrete PEmpty) (Type) :=
  Completeness.hasLimitsOfShape (Type) Cardinal.aleph0.{0} _

example : HasLimitsOfShape (Discrete (ULift.{1} ℕ)) (Type) :=
  Completeness.hasLimitsOfShape (Type) Cardinal.aleph0.{0} _

example : HasLimitsOfShape (SingleObj ℕ) (Type) :=
  Completeness.hasLimitsOfShape (Type) Cardinal.aleph0.{0} _

end Concrete

end CategoryTheory.Presentable.CompletenessTest
