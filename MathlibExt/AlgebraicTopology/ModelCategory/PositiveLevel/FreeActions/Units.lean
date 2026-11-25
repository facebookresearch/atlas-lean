/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.PositiveLevel.FreeActions.Components

/-!
# Original input and Day unit maps of finite-action free R-modules

The original left Kan extension unit and its actual naturality combine with
the original Day tensor extension unit. These are the original whole maps
used to compare free-module coefficient arrows, for every action input.
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

/-- The original finite-action input diagram in the Day category. -/
def actionInputDiagramFunctor (n : ℕ) : degreeActionCategory (C := C) n ⥤ DayFunctor I C :=
  (degreeActionInclusion n).lan ⋙ (DayFunctor.equiv I C).symm.functor

/-- The actual original left Kan unit, typed at the original finite alphabet. -/
def actionInputUnit (n : ℕ) (A : degreeActionCategory (C := C) n) (a : degreeActionIndex n) :
    A.obj a ⟶ ((actionInputDiagramFunctor n).obj A).functor.obj (card n) :=
  ((degreeActionInclusion n).leftKanExtensionUnit A).app a

omit [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorLeft Z)]
  [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorRight Z)] in
/-- The actual input unit keeps naturality of every original finite-action map. -/
theorem actionInputUnit_naturality (n : ℕ) {A B : degreeActionCategory (C := C) n}
    (f : A ⟶ B) (a : degreeActionIndex n) :
    actionInputUnit n A a ≫ ((actionInputDiagramFunctor n).map f).natTrans.app (card n) =
      f.app a ≫ actionInputUnit n B a :=
  (congr_app ((degreeActionInclusion n).lanUnit.naturality f) a).symm

variable (R : DayFunctor I C) [MonObj R]

/-- The original free-module arrow has exactly the original R tensor of the original input-diagram
map. -/
theorem actionFreeMap_hom (n : ℕ) {A B : degreeActionCategory (C := C) n} (f : A ⟶ B) :
    ((degreeActionFreeAt R n).map f).hom = R ◁ (actionInputDiagramFunctor n).map f := rfl

/-- Every original composite coefficient unit has its actual input-unit and Day-unit formula. -/
theorem actionTensorUnit_app (n : ℕ) (A : degreeActionCategory (C := C) n) (x : I)
    (a : degreeActionIndex n) :
    (actionTensorUnit R n A).app (x, a) =
      (R.functor.obj x ◁ actionInputUnit n A a) ≫
        (DayFunctor.η R ((actionInputDiagramFunctor n).obj A)).app (x, card n) := by
  let G := (actionInputDiagramFunctor n).obj A
  let P := (𝟭 I).prod (degreeActionInclusion n)
  have ht : (Functor.whiskerLeft P (DayFunctor.η R G) ≫
      (Functor.associator P (tensor I) (R ⊗ G).functor).inv).app (x, a) =
        (DayFunctor.η R G).app (x, card n) := by
    change (DayFunctor.η R G).app (x, card n) ≫ 𝟙 _ = (DayFunctor.η R G).app (x, card n)
    exact Category.comp_id _
  have halpha :
      (ExternalProduct.extensionUnitRight G.functor
        ((degreeActionInclusion n).leftKanExtensionUnit A) R.functor).app (x, a) =
          R.functor.obj x ◁ actionInputUnit n A a := by
    simp [ExternalProduct.extensionUnitRight, actionInputUnit]
    rfl
  have hs : (actionTensorUnit R n A).app (x, a) =
      (R.functor.obj x ◁ actionInputUnit n A a) ≫
        (Functor.whiskerLeft P (DayFunctor.η R G) ≫
          (Functor.associator P (tensor I) (R ⊗ G).functor).inv).app (x, a) :=
    congrArg (fun t => t ≫ (Functor.whiskerLeft P (DayFunctor.η R G) ≫
      (Functor.associator P (tensor I) (R ⊗ G).functor).inv).app (x, a)) halpha
  exact hs.trans (congrArg (fun t => (R.functor.obj x ◁ actionInputUnit n A a) ≫ t) ht)

/-- The actual whole coefficient unit is natural in every original finite-action input map. -/
theorem actionTensorUnit_naturality_app (n : ℕ) {A B : degreeActionCategory (C := C) n}
    (f : A ⟶ B) (x : I) (a : degreeActionIndex n) :
    (actionTensorUnit R n A).app (x, a) ≫ ((degreeActionFreeAt R n).map f).hom.natTrans.app
        (x ⊗ card n) =
      (R.functor.obj x ◁ f.app a) ≫ (actionTensorUnit R n B).app (x, a) := by
  let GA := (actionInputDiagramFunctor n).obj A
  let GB := (actionInputDiagramFunctor n).obj B
  let g : GA ⟶ GB := (actionInputDiagramFunctor n).map f
  let uA : A.obj a ⟶ GA.functor.obj (card n) := actionInputUnit n A a
  let uB : B.obj a ⟶ GB.functor.obj (card n) := actionInputUnit n B a
  let etaA := (DayFunctor.η R GA).app (x, card n)
  let etaB := (DayFunctor.η R GB).app (x, card n)
  have hu : uA ≫ g.natTrans.app (card n) = f.app a ≫ uB := actionInputUnit_naturality n f a
  have he : etaA ≫ (R ◁ g).natTrans.app (x ⊗ card n) =
      (R.functor.obj x ◁ g.natTrans.app (card n)) ≫ etaB :=
    LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit_comp_ι_map_whiskerLeft_app
        C R g x (card n)
  have hA : (actionTensorUnit R n A).app (x, a) = (R.functor.obj x ◁ uA) ≫ etaA :=
    actionTensorUnit_app R n A x a
  have hB : (actionTensorUnit R n B).app (x, a) = (R.functor.obj x ◁ uB) ≫ etaB :=
    actionTensorUnit_app R n B x a
  calc
    _ = ((R.functor.obj x ◁ uA) ≫ etaA) ≫ (R ◁ g).natTrans.app (x ⊗ card n) :=
      congrArg (fun t => t ≫ (R ◁ g).natTrans.app (x ⊗ card n)) hA
    _ = (R.functor.obj x ◁ uA) ≫ (etaA ≫ (R ◁ g).natTrans.app (x ⊗ card n)) := Category.assoc _ _ _
    _ = (R.functor.obj x ◁ uA) ≫ ((R.functor.obj x ◁ g.natTrans.app (card n)) ≫ etaB) :=
      congrArg (fun t => (R.functor.obj x ◁ uA) ≫ t) he
    _ = ((R.functor.obj x ◁ uA) ≫ (R.functor.obj x ◁ g.natTrans.app (card n))) ≫ etaB :=
      (Category.assoc _ _ _).symm
    _ = (R.functor.obj x ◁ (uA ≫ g.natTrans.app (card n))) ≫ etaB :=
      congrArg (fun t => t ≫ etaB)
          (whiskerLeft_comp (R.functor.obj x) uA (g.natTrans.app (card n))).symm
    _ = (R.functor.obj x ◁ (f.app a ≫ uB)) ≫ etaB :=
      congrArg (fun t => (R.functor.obj x ◁ t) ≫ etaB) hu
    _ = ((R.functor.obj x ◁ f.app a) ≫ (R.functor.obj x ◁ uB)) ≫ etaB :=
      congrArg (fun t => t ≫ etaB) (whiskerLeft_comp (R.functor.obj x) (f.app a) uB)
    _ = (R.functor.obj x ◁ f.app a) ≫ ((R.functor.obj x ◁ uB) ≫ etaB) := Category.assoc _ _ _
    _ = _ := congrArg (fun t => (R.functor.obj x ◁ f.app a) ≫ t) hB.symm

end HomotopicalAlgebra.PositiveLevelModel
