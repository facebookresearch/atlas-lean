/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.PositiveLevel.FreeActions.Units
public import MathlibExt.AlgebraicTopology.ModelCategory.PositiveLevel.FreeActions.Coefficients

/-!
# Every original map in finite-action free R-module coefficient comparisons

The original coefficient maps and both original pointwise Kan comparison
legs retain every finite-action input arrow. Their naturality is proved
through the actual Lan/Day unit equations and all original decomposition legs.
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

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [HasColimitsOfSize.{0, 0} C]
  [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorLeft Z)]
  [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorRight Z)]
  (R : DayFunctor I C)

/-- The original coefficient diagram map induced by an arbitrary finite-action arrow. -/
def actionComponentMap (n m : ℕ) {A B : degreeActionCategory (C := C) n} (f : A ⟶ B) :
    actionComponentDiagram R n m A ⟶ actionComponentDiagram R n m B :=
  Functor.whiskerLeft (CostructuredArrow.proj (actionTensorIndex n) (card m))
    ((externalProductBifunctor I (degreeActionIndex n) C).map ⟨𝟙 R.functor, f⟩)

omit [HasColimitsOfSize.{0, 0} C]
  [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorLeft Z)]
  [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorRight Z)] in
/-- Every original coefficient arrow retains the same scalar object and original action-input
component. -/
theorem actionComponentMap_app (n m : ℕ) {A B : degreeActionCategory (C := C) n} (f : A ⟶ B)
    (d : CostructuredArrow (actionTensorIndex n) (card m)) :
    (actionComponentMap R n m f).app d = R.functor.obj d.left.1 ◁ f.app d.left.2 := by
  simp [actionComponentMap]

variable [MonObj R]

/-- The actual inverse pointwise comparison sends every original coefficient leg to its original
free-module unit leg.
-/
theorem actionComponentIso_inv_leg (n m : ℕ) (A : degreeActionCategory (C := C) n)
    (d : CostructuredArrow (actionTensorIndex n) (card m)) :
    colimit.ι (actionComponentDiagram R n m A) d ≫ (actionComponentIso R n m A).inv =
      (actionTensorUnit R n A).app d.left ≫ ((degreeActionFreeAt R n).obj A).X.functor.map d.hom :=
          by
  let F := ((degreeActionFreeAt R n).obj A).X.functor
  let _ : F.IsLeftKanExtension (actionTensorUnit R n A) := actionTensorUnit_isLeftKanExtension R n A
  let hPoint := Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension F (actionTensorUnit R n A)
      (card m)
  have h : (actionTensorUnit R n A).app d.left ≫ F.map d.hom ≫ (actionComponentIso R n m A).hom =
      colimit.ι (actionComponentDiagram R n m A) d := hPoint.ι_isoColimit_hom d
  have hh := congrArg (fun t => t ≫ (actionComponentIso R n m A).inv) h
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hh.symm

/-- The actual inverse comparison is natural at every original coefficient leg and action-input
arrow. -/
theorem actionComponentIso_inv_leg_naturality (n m : ℕ) {A B : degreeActionCategory (C := C) n}
    (f : A ⟶ B) (d : CostructuredArrow (actionTensorIndex n) (card m)) :
    (colimit.ι (actionComponentDiagram R n m A) d ≫ (actionComponentIso R n m A).inv) ≫
      ((degreeActionFreeAt R n).map f).hom.natTrans.app (card m) =
        (actionComponentMap R n m f).app d ≫
          colimit.ι (actionComponentDiagram R n m B) d ≫ (actionComponentIso R n m B).inv := by
  let FA := ((degreeActionFreeAt R n).obj A).X.functor
  let FB := ((degreeActionFreeAt R n).obj B).X.functor
  let ff := ((degreeActionFreeAt R n).map f).hom.natTrans
  let uA := (actionTensorUnit R n A).app d.left
  let uB := (actionTensorUnit R n B).app d.left
  let k := R.functor.obj d.left.1 ◁ f.app d.left.2
  have hiA : colimit.ι (actionComponentDiagram R n m A) d ≫ (actionComponentIso R n m A).inv = uA ≫
      FA.map d.hom :=
    actionComponentIso_inv_leg R n m A d
  have hiB : colimit.ι (actionComponentDiagram R n m B) d ≫ (actionComponentIso R n m B).inv = uB ≫
      FB.map d.hom :=
    actionComponentIso_inv_leg R n m B d
  have hn : FA.map d.hom ≫ ff.app (card m) = ff.app ((actionTensorIndex n).obj d.left) ≫ FB.map
      d.hom :=
    ff.naturality d.hom
  have hu : uA ≫ ff.app ((actionTensorIndex n).obj d.left) = k ≫ uB :=
    actionTensorUnit_naturality_app R n f d.left.1 d.left.2
  calc
    _ = (uA ≫ FA.map d.hom) ≫ ff.app (card m) := congrArg (fun t => t ≫ ff.app (card m)) hiA
    _ = uA ≫ (FA.map d.hom ≫ ff.app (card m)) := Category.assoc _ _ _
    _ = uA ≫ (ff.app ((actionTensorIndex n).obj d.left) ≫ FB.map d.hom) := congrArg
        (fun t => uA ≫ t) hn
    _ = (uA ≫ ff.app ((actionTensorIndex n).obj d.left)) ≫ FB.map d.hom :=
        (Category.assoc _ _ _).symm
    _ = (k ≫ uB) ≫ FB.map d.hom := congrArg (fun t => t ≫ FB.map d.hom) hu
    _ = k ≫ (uB ≫ FB.map d.hom) := Category.assoc _ _ _
    _ = k ≫ (colimit.ι (actionComponentDiagram R n m B) d ≫ (actionComponentIso R n m B).inv) :=
      congrArg (fun t => k ≫ t) hiB.symm
    _ = _ := by rw [actionComponentMap_app]

/-- The original whole coefficient comparison is natural for every actual input arrow. -/
theorem actionComponentIso_naturality (n m : ℕ) {A B : degreeActionCategory (C := C) n} (f : A ⟶ B)
    :
    ((degreeActionFreeAt R n).map f).hom.natTrans.app (card m) ≫ (actionComponentIso R n m B).hom =
      (actionComponentIso R n m A).hom ≫ colimMap (actionComponentMap R n m f) := by
  apply (cancel_epi (actionComponentIso R n m A).inv).mp
  apply colimit.hom_ext
  intro d
  have h := actionComponentIso_inv_leg_naturality R n m f d
  have hh := congrArg (fun t => t ≫ (actionComponentIso R n m B).hom) h
  have hLeg : colimit.ι (actionComponentDiagram R n m A) d ≫ (actionComponentIso R n m A).inv ≫
      ((degreeActionFreeAt R n).map f).hom.natTrans.app (card m) ≫ (actionComponentIso R n m B).hom
          =
        (actionComponentMap R n m f).app d ≫ colimit.ι (actionComponentDiagram R n m B) d := by
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hh
  have hcancel : (actionComponentIso R n m A).inv ≫ (actionComponentIso R n m A).hom ≫
      colimMap (actionComponentMap R n m f) = colimMap (actionComponentMap R n m f) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ colimMap (actionComponentMap R n m f))
        (actionComponentIso R n m A).inv_hom_id).trans (Category.id_comp _))
  exact hLeg.trans ((ι_colimMap (actionComponentMap R n m f) d).symm.trans
    (congrArg (fun t => colimit.ι (actionComponentDiagram R n m A) d ≫ t) hcancel.symm))

end HomotopicalAlgebra.PositiveLevelModel
