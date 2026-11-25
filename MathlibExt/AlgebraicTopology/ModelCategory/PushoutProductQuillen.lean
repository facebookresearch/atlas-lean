/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.PushoutProductAxiom
public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenAdjunction

/-!
# Tensor Quillen adjunctions from pushout-products

The adjunctions are the actual closed tensor adjunction and its braided
right-tensor transport. Their Quillen proofs require the selected
pushout-product laws and a cofibrant tensor factor. No unit witness is used.
The right-tensor Hom correspondence, unit and counit retain the original
braiding and closed evaluation maps.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe v u

open CategoryTheory Limits MonoidalCategory BraidedCategory
open scoped MonoidalCategory

namespace HomotopicalAlgebra

section ClosedAdjunction

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [MonoidalClosed C]

/-- The actual right tensor adjunction, obtained from the specified closed
adjunction through the specified braiding. Its right adjoint is unchanged. -/
noncomputable def tensorRightIhomAdjunction (K : C) :
    tensorRight K ⊣ ihom K :=
  (ihom.adjunction K).ofNatIsoLeft (tensorLeftIsoTensorRight K)

/-- The right tensor transpose is the original closed transpose after the
literal braiding from left tensor to right tensor. -/
@[simp, nolint simpNF] -- simpNF only sees `tensorRight` unfolding in the hom type
theorem tensorRightIhomAdjunction_homEquiv_apply
    (K : C) {X Y : C} (f : X ⊗ K ⟶ Y) :
    (tensorRightIhomAdjunction K).homEquiv X Y f =
      MonoidalClosed.curry ((β_ K X).hom ≫ f) := by
  rw [tensorRightIhomAdjunction, Adjunction.homEquiv_ofNatIsoLeft_apply]
  exact MonoidalClosed.homEquiv_apply_eq _

/-- The inverse right tensor transpose uses the inverse of the same
braiding and the original closed uncurrying map. -/
@[simp, nolint simpNF] -- simpNF only sees `tensorRight` unfolding in the hom type
theorem tensorRightIhomAdjunction_homEquiv_symm_apply
    (K : C) {X Y : C} (g : X ⟶ (ihom K).obj Y) :
    ((tensorRightIhomAdjunction K).homEquiv X Y).symm g =
      (β_ K X).inv ≫ MonoidalClosed.uncurry g := by
  rw [tensorRightIhomAdjunction, Adjunction.homEquiv_ofNatIsoLeft_symm_apply]
  rw [MonoidalClosed.homEquiv_symm_apply_eq]
  rfl

/-- The right tensor unit is the original closed unit followed by the
internal-Hom image of the actual braiding. -/
@[simp]
theorem tensorRightIhomAdjunction_unit_app (K X : C) :
    (tensorRightIhomAdjunction K).unit.app X =
      (ihom.coev K).app X ≫ (ihom K).map (β_ K X).hom :=
  rfl

/-- The right tensor counit is inverse braiding followed by the original
closed evaluation. -/
@[simp]
theorem tensorRightIhomAdjunction_counit_app (K Y : C) :
    (tensorRightIhomAdjunction K).counit.app Y =
      (β_ K ((ihom K).obj Y)).inv ≫ (ihom.ev K).app Y :=
  rfl

/-- The right transpose preserves the original source-map action. -/
theorem tensorRightIhomAdjunction_homEquiv_naturality_left
    (K : C) {X X' Y : C} (a : X' ⟶ X) (f : X ⊗ K ⟶ Y) :
    (tensorRightIhomAdjunction K).homEquiv X' Y ((a ▷ K) ≫ f) =
      a ≫ (tensorRightIhomAdjunction K).homEquiv X Y f :=
  (tensorRightIhomAdjunction K).homEquiv_naturality_left a f

/-- The right transpose preserves the original target-map action. -/
theorem tensorRightIhomAdjunction_homEquiv_naturality_right
    (K : C) {X Y Y' : C} (f : X ⊗ K ⟶ Y) (b : Y ⟶ Y') :
    (tensorRightIhomAdjunction K).homEquiv X Y' (f ≫ b) =
      (tensorRightIhomAdjunction K).homEquiv X Y f ≫ (ihom K).map b :=
  (tensorRightIhomAdjunction K).homEquiv_naturality_right f b

end ClosedAdjunction

namespace MonoidalPushoutProductAxiom

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C]
variable (hPP : MonoidalPushoutProductAxiom C)
include hPP

/-- The original fixed-left closed tensor adjunction is Quillen from the
pushout-product part of the axioms alone. -/
theorem ihomAdjunction_isQuillenAdjunction
    (K : C) [IsCofibrant K] :
    (ihom.adjunction K).IsQuillenAdjunction where
  preservesCofibrations := fun _ _ i hi ↦ hPP.whiskerLeft_mem_cofibrations K i hi
  preservesTrivialCofibrations :=
    fun _ _ i hi ↦ hPP.whiskerLeft_mem_trivialCofibrations K i hi

/-- The original fixed-right tensor adjunction is Quillen. This proof uses
the actual right initial-map pushout comparison and the left trivial law. -/
theorem tensorRightIhomAdjunction_isQuillenAdjunction
    (K : C) [IsCofibrant K] :
    (tensorRightIhomAdjunction K).IsQuillenAdjunction where
  preservesCofibrations := fun _ _ i hi ↦ hPP.whiskerRight_mem_cofibrations i K hi
  preservesTrivialCofibrations :=
    fun _ _ i hi ↦ hPP.whiskerRight_mem_trivialCofibrations i K hi

/-- The internal Hom by a cofibrant object preserves actual fibrations,
before the unit condition has been established. -/
theorem ihom_mem_fibrations
    (K : C) [IsCofibrant K] {X Y : C} (p : X ⟶ Y)
    (hp : fibrations C p) : fibrations C ((ihom K).map p) := by
  let _ : (ihom.adjunction K).IsQuillenAdjunction :=
    hPP.ihomAdjunction_isQuillenAdjunction K
  exact Adjunction.IsQuillenAdjunction.preservesFibrations
    (adj := ihom.adjunction K) p hp

/-- The same internal-Hom functor preserves actual trivial fibrations. -/
theorem ihom_mem_trivialFibrations
    (K : C) [IsCofibrant K] {X Y : C} (p : X ⟶ Y)
    (hp : trivialFibrations C p) : trivialFibrations C ((ihom K).map p) := by
  let _ : (ihom.adjunction K).IsQuillenAdjunction :=
    hPP.ihomAdjunction_isQuillenAdjunction K
  exact Adjunction.IsQuillenAdjunction.preservesTrivialFibrations
    (adj := ihom.adjunction K) p hp

/-- Internal Hom from a cofibrant factor into a fibrant object is fibrant,
for the actual selected model and closed structure. -/
theorem isFibrant_ihom_obj (K Y : C) [IsCofibrant K] [IsFibrant Y] :
    IsFibrant ((ihom K).obj Y) := by
  let _ : (ihom.adjunction K).IsQuillenAdjunction :=
    hPP.ihomAdjunction_isQuillenAdjunction K
  exact Adjunction.IsQuillenAdjunction.preservesFibrantObjects
    (adj := ihom.adjunction K) inferInstance

end MonoidalPushoutProductAxiom

end HomotopicalAlgebra
