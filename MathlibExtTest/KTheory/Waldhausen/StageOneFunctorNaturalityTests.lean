/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageOneFunctorNaturality

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v uD vD uE vE
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject Simplicial
namespace MathlibExtTest.StageOneFunctorNaturality
open CategoryTheory.Waldhausen.SConstruction
variable {C : Type u} [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]
variable {D : Type uD} [Category.{vD} D] [HasZeroObject D] [WaldhausenCategoryWithoutGluing D]
variable {F : C ⥤ D} (hF : F.IsWaldhausenExact)

/-- An arbitrary original exact functor has the whole S₁ diagram comparison, without a zero
equation. -/
def originalDiagramComparison (X : C) :
    stageOneDiagram C X ⋙ F ≅ stageOneDiagram D (F.obj X) := stageOneDiagramPostcompIso hF X

/-- The same comparison lives in the original stage category. -/
def originalStageComparison (X : C) :
    (hF.mapStage 1).obj ((stageOne C).obj X) ≅ (stageOne D).obj (F.obj X) :=
  stageOnePostcompStageIso hF X

/-- The same original exact functor has its entire natural S₁ insertion square. -/
def originalWholeFunctorComparison : stageOne C ⋙ hF.mapStage 1 ≅ F ⋙ stageOne D :=
  stageOnePostcompNatIso hF

/-- Every original ordinal interval pullback retains the same whole natural comparison. -/
def originalIntervalComparison {a : SimplexCategory} (f : a ⟶ ⦋1⦌) :
    stageOne C ⋙ reindexStage (C := C) f ⋙ hF.mapStage a.len ≅
      F ⋙ stageOne D ⋙ reindexStage (C := D) f := stageOneIntervalPostcompNatIso hF f

variable {E : Type uE} [Category.{vE} E] [HasZeroObject E] [WaldhausenCategoryWithoutGluing E]
variable {G : D ⥤ E}

/-- Three independent object and morphism universes retain the canonical original zero composite. -/
theorem originalMixedZeroComposition (hG : G.IsWaldhausenExact) :
    (stageOneFunctorZeroIso (hF.comp hG)).hom =
      G.map (stageOneFunctorZeroIso hF).hom ≫ (stageOneFunctorZeroIso hG).hom :=
  stageOneFunctorZeroIso_comp hF hG

end MathlibExtTest.StageOneFunctorNaturality
