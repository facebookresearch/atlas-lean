/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.PositiveLevel.FreeActions.Basic
public import Mathlib.CategoryTheory.Monoidal.ExternalProduct.KanExtension

/-!
# Actual finite-action free R-module coefficient diagrams

The original free module tensor is the left Kan extension of the actual scalar
and action input along the original block tensor functor. The pointwise Kan
extension comparison exposes its original coefficient diagram at every degree.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe v u

open CategoryTheory Limits MonoidalCategory MonObj
open CategoryTheory.MonoidalCategory
open CategoryTheory.Operad.SmallFinBijGroupoid
open scoped CategoryTheory.MonObj CategoryTheory.Prod
open scoped CategoryTheory.MonoidalCategory.ExternalProduct

namespace HomotopicalAlgebra.PositiveLevelModel

local notation "I" => CategoryTheory.Operad.SmallFinBijGroupoid

/-- The original complement-first block tensor functor with its Sigma_n input action. -/
abbrev actionTensorIndex (n : ℕ) : I × degreeActionIndex n ⥤ I :=
  (𝟭 I).prod (degreeActionInclusion n) ⋙ tensor I

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [HasColimitsOfSize.{0, 0} C]
  [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorLeft Z)]
  [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorRight Z)]
  (R : DayFunctor I C) [MonObj R]

/-- The original composite Kan-extension unit defining the free R-module coefficients. -/
def actionTensorUnit (n : ℕ) (A : degreeActionCategory (C := C) n) :
    R.functor ⊠ A ⟶ actionTensorIndex n ⋙ ((degreeActionFreeAt R n).obj A).X.functor :=
  let G := (DayFunctor.equiv I C).symm.functor.obj ((degreeActionInclusion n).lan.obj A)
  let P := (𝟭 I).prod (degreeActionInclusion n)
  ExternalProduct.extensionUnitRight G.functor
      ((degreeActionInclusion n).leftKanExtensionUnit A) R.functor ≫
    Functor.whiskerLeft P (DayFunctor.η R G) ≫
      (Functor.associator P (tensor I) (R ⊗ G).functor).inv

/-- The actual original free module is the Kan extension along the original block index. -/
theorem actionTensorUnit_isLeftKanExtension (n : ℕ) (A : degreeActionCategory (C := C) n) :
    ((degreeActionFreeAt R n).obj A).X.functor.IsLeftKanExtension (actionTensorUnit R n A) := by
  let L := degreeActionInclusion n
  let G := (DayFunctor.equiv I C).symm.functor.obj (L.lan.obj A)
  let P := (𝟭 I).prod L
  let α : R.functor ⊠ A ⟶ P ⋙ R.functor ⊠ G.functor :=
    ExternalProduct.extensionUnitRight G.functor (L.leftKanExtensionUnit A) R.functor
  let _ : (R.functor ⊠ G.functor).IsLeftKanExtension α :=
    (ExternalProduct.isPointwiseLeftKanExtensionExtensionUnitRight G.functor
      (L.leftKanExtensionUnit A) R.functor
      (L.isPointwiseLeftKanExtensionLeftKanExtensionUnit A)).isLeftKanExtension
  let β : R.functor ⊠ G.functor ⟶ tensor I ⋙ (R ⊗ G).functor := DayFunctor.η R G
  have hβ : (R ⊗ G).functor.IsLeftKanExtension β := inferInstance
  exact (Functor.isLeftKanExtension_iff_postcompose (α := α) (L' := tensor I)
    (P ⋙ tensor I) (Iso.refl _) β (actionTensorUnit R n A) (by
      change α ≫ Functor.whiskerLeft P β ≫ (Functor.associator P (tensor I) (R ⊗ G).functor).inv ≫
        Functor.whiskerRight (𝟙 (P ⋙ tensor I)) (R ⊗ G).functor =
          α ≫ Functor.whiskerLeft P β ≫ (Functor.associator P (tensor I) (R ⊗ G).functor).inv
      rw [Functor.whiskerRight_id', Category.comp_id])).mp hβ

/-- The entire original coefficient diagram of the actual free module at degree m. -/
abbrev actionComponentDiagram (n m : ℕ) (A : degreeActionCategory (C := C) n) :
    CostructuredArrow (actionTensorIndex n) (card m) ⥤ C :=
  CostructuredArrow.proj (actionTensorIndex n) (card m) ⋙ R.functor ⊠ A

/-- Every actual original degree of the finite-action free module is its original coefficient
colimit. -/
def actionComponentIso (n m : ℕ) (A : degreeActionCategory (C := C) n) :
    ((degreeActionFreeAt R n).obj A).X.functor.obj (card m) ≅ colimit
        (actionComponentDiagram R n m A) := by
  let _ : ((degreeActionFreeAt R n).obj A).X.functor.IsLeftKanExtension (actionTensorUnit R n A) :=
    actionTensorUnit_isLeftKanExtension R n A
  exact Functor.LeftExtension.IsPointwiseLeftKanExtensionAt.isoColimit
    (Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension _ (actionTensorUnit R n A) (card m))

end HomotopicalAlgebra.PositiveLevelModel
