/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageOneIntervalInsertion
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWaldhausenFunctoriality
public import Mathlib.CategoryTheory.Whiskering

/-!
# Original S₁ insertion is naturally compatible with exact functors

An exact functor preserves zero objects up to their canonical zero
isomorphism. On the original S₁ insertion this isomorphism supplies each
diagonal component, and the actual off-diagonal component is the identity.
These components compare the complete original diagrams without a strict
chosen-zero equality hypothesis.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v uD vD uE vE
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject Simplicial

namespace CategoryTheory.Waldhausen.SConstruction

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]
variable {D : Type uD} [Category.{vD} D] [HasZeroObject D] [WaldhausenCategoryWithoutGluing D]
variable {F : C ⥤ D} (hF : F.IsWaldhausenExact)

/-- The actual exact functor's image of the original chosen zero has its canonical zero isomorphism.
-/
def stageOneFunctorZeroIso : F.obj (0 : C) ≅ (0 : D) :=
  (hF.map_isZero (isZero_zero C)).isoZero

/-- The original S₁ diagram comparison uses that zero isomorphism on diagonals and identity
elsewhere. -/
def stageOneDiagramPostcompIsoComponent (X : C) (A : Ar 1) :
    (stageOneDiagram C X ⋙ F).obj A ≅ (stageOneDiagram D (F.obj X)).obj A := by
  by_cases h : A.left = A.right
  · simpa only [Functor.comp_obj, stageOneDiagram, stageOneDiagramObj, ite_eq_left h] using
      stageOneFunctorZeroIso hF
  · simpa only [Functor.comp_obj, stageOneDiagram, stageOneDiagramObj, ite_eq_right h] using
      Iso.refl (F.obj X)

/-- The complete original S₁ postcomposition diagram has its actual canonical natural isomorphism.
-/
def stageOneDiagramPostcompIso (X : C) :
    stageOneDiagram C X ⋙ F ≅ stageOneDiagram D (F.obj X) :=
  NatIso.ofComponents (stageOneDiagramPostcompIsoComponent hF X) (by
    intro A B f
    by_cases ha : A.left = A.right
    · have hZ : IsZero ((stageOneDiagram C X ⋙ F).obj A) := by
        change IsZero (F.obj (stageOneDiagramObj C X A))
        rw [stageOneDiagramObj_of_eq C X ha]
        exact hF.map_isZero (isZero_zero C)
      exact hZ.eq_of_src _ _
    · by_cases hb : B.left = B.right
      · have hZ : IsZero ((stageOneDiagram D (F.obj X)).obj B) := by
          change IsZero (stageOneDiagramObj D (F.obj X) B)
          rw [stageOneDiagramObj_of_eq D (F.obj X) hb]
          exact isZero_zero D
        exact hZ.eq_of_tgt _ _
      · have hA := ar1_eq_interval01_of_ne ha
        have hB := ar1_eq_interval01_of_ne hb
        subst A
        subst B
        have hf : f = 𝟙 _ := Arrow.hom_ext _ _ (Subsingleton.elim _ _) (Subsingleton.elim _ _)
        subst f
        simp only [Functor.map_id, Category.id_comp, Category.comp_id])

set_option backward.isDefEq.respectTransparency false in
/-- The complete diagram comparison retains the actual identity at the original coefficient
interval. -/
theorem stageOneDiagramPostcompIso_hom_interval (X : C) :
    (stageOneDiagramPostcompIso hF X).hom.app (interval (0 : Fin 2) 1 (by decide)) =
      𝟙 (F.obj X) := by
  dsimp only [stageOneDiagramPostcompIso, NatIso.ofComponents_hom_app,
    stageOneDiagramPostcompIsoComponent]
  simp only [interval, Arrow.mk_left, Arrow.mk_right,
    dite_eq_right (by decide : ¬ (0 : Fin 2) = 1), eq_mpr_eq_cast]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The actual inverse comparison also retains the coefficient identity. -/
theorem stageOneDiagramPostcompIso_inv_interval (X : C) :
    (stageOneDiagramPostcompIso hF X).inv.app (interval (0 : Fin 2) 1 (by decide)) =
      𝟙 (F.obj X) := by
  dsimp only [stageOneDiagramPostcompIso, NatIso.ofComponents_inv_app,
    stageOneDiagramPostcompIsoComponent]
  simp only [interval, Arrow.mk_left, Arrow.mk_right,
    dite_eq_right (by decide : ¬ (0 : Fin 2) = 1), eq_mpr_eq_cast]
  rfl

/-- This comparison is an isomorphism of the actual original S₁ stage objects. -/
def stageOnePostcompStageIso (X : C) :
    (hF.mapStage 1).obj ((stageOne C).obj X) ≅ (stageOne D).obj (F.obj X) :=
  ObjectProperty.isoMk (stageProperty D 1) (stageOneDiagramPostcompIso hF X)

set_option backward.isDefEq.respectTransparency false in
/-- The original diagram comparison commutes with the complete original object-map functor. -/
theorem stageOnePostcompStageIso_naturality {X Y : C} (f : X ⟶ Y) :
    (stageOne C ⋙ hF.mapStage 1).map f ≫ (stageOnePostcompStageIso hF Y).hom =
      (stageOnePostcompStageIso hF X).hom ≫ (F ⋙ stageOne D).map f := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext A
  by_cases hA : A.left = A.right
  · have hZ : IsZero (F.obj (stageOneDiagramObj C X A)) := by
      rw [stageOneDiagramObj_of_eq C X hA]
      exact hF.map_isZero (isZero_zero C)
    exact hZ.eq_of_src _ _
  · have hInterval := ar1_eq_interval01_of_ne hA
    subst A
    change F.map f ≫ (stageOneDiagramPostcompIso hF Y).hom.app
        (interval (0 : Fin 2) 1 (by decide)) =
      (stageOneDiagramPostcompIso hF X).hom.app
        (interval (0 : Fin 2) 1 (by decide)) ≫ F.map f
    simp only [stageOneDiagramPostcompIso, NatIso.ofComponents_hom_app,
      stageOneDiagramPostcompIsoComponent]
    simp only [interval, Arrow.mk_left, Arrow.mk_right, dite_eq_right (by decide : ¬ (0 : Fin 2)
        = 1),
      eq_mpr_eq_cast, cast_eq, Iso.refl_hom, Category.comp_id]
    exact (Category.id_comp (F.map f)).symm

/-- The complete original S₁ insertion square is a natural isomorphism for every exact functor. -/
def stageOnePostcompNatIso : stageOne C ⋙ hF.mapStage 1 ≅ F ⋙ stageOne D :=
  NatIso.ofComponents (stageOnePostcompStageIso hF) (stageOnePostcompStageIso_naturality hF)

/-- The complete interval insertion comparison is the original S₁ comparison pulled back along its
ordinal map. -/
def stageOneIntervalPostcompNatIso {a : SimplexCategory} (f : a ⟶ ⦋1⦌) :
    stageOne C ⋙ reindexStage (C := C) f ⋙ hF.mapStage a.len ≅
      F ⋙ stageOne D ⋙ reindexStage (C := D) f := by
  let e := Functor.isoWhiskerRight (stageOnePostcompNatIso hF) (reindexStage (C := D) f)
  have h := hF.mapStage_reindex f
  change stageOne C ⋙ (reindexStage (C := C) f ⋙ hF.mapStage a.len) ≅ _
  rw [h]
  exact e

/-- The actual mapped zero isomorphism has the original unique map as its forward component. -/
theorem stageOneFunctorZeroIso_hom :
    (stageOneFunctorZeroIso hF).hom = (hF.map_isZero (isZero_zero C)).to_ (0 : D) := rfl

/-- The actual mapped zero isomorphism has the original unique map as its inverse component. -/
theorem stageOneFunctorZeroIso_inv :
    (stageOneFunctorZeroIso hF).inv = (isZero_zero D).to_ (F.obj (0 : C)) := by
  exact (isZero_zero D).eq_of_src _ _

/-- The canonical image-zero isomorphism of the identity is the actual identity. -/
theorem stageOneFunctorZeroIso_id :
    (stageOneFunctorZeroIso (Functor.IsWaldhausenExact.id (C := C))).hom = 𝟙 (0 : C) := by
  exact (isZero_zero C).eq_of_src _ _

variable {E : Type uE} [Category.{vE} E] [HasZeroObject E] [WaldhausenCategoryWithoutGluing E]
variable {G : D ⥤ E}

/-- Original source-first composition retains the same canonical zero-isomorphism composite. -/
theorem stageOneFunctorZeroIso_comp (hG : G.IsWaldhausenExact) :
    (stageOneFunctorZeroIso (hF.comp hG)).hom =
      G.map (stageOneFunctorZeroIso hF).hom ≫ (stageOneFunctorZeroIso hG).hom := by
  exact (hG.map_isZero (hF.map_isZero (isZero_zero C))).eq_of_src _ _

end CategoryTheory.Waldhausen.SConstruction
