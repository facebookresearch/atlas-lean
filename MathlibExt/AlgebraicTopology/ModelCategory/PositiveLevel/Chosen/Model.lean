/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.PositiveLevel.Sources.ChosenRanks
import MathlibExt.AlgebraicTopology.ModelCategory.PositiveLevel.Sources.ChosenAcyclicity
import MathlibExt.AlgebraicTopology.ModelCategory.PositiveLevel.FreeActions.Below
import MathlibExt.AlgebraicTopology.ModelCategory.PositiveLevel.Restriction
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenAdjunction

/-!
# Actual chosen finite-action level R-module models

Both original free I_n/J_n families admit the actual common-rank small-object
arguments. Their exact lifting classes and the earned original residual
coefficient acyclicity construct the full model on the same R-module carrier.
The positive variant retains precisely the original degrees n>0.
-/

set_option autoImplicit false
noncomputable section
universe w v u

open CategoryTheory Limits MorphismProperty MonoidalCategory MonObj
open CategoryTheory.MonoidalCategory
open CategoryTheory.Operad.SmallFinBijGroupoid
open scoped CategoryTheory.MonObj MonoidalClosed

namespace HomotopicalAlgebra.PositiveLevelModel.Chosen

local notation "I" => CategoryTheory.Operad.SmallFinBijGroupoid

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [baseModel : ModelCategory C] [HasColimitsOfSize.{w, w} C] [HasLimitsOfSize.{w, w} C]
  [IsLocallyPresentable.{w} C]

local instance chosenBaseSmallColimits : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink.{0, 0, w, w} C
local instance chosenBaseSmallLimits : HasLimitsOfSize.{0, 0} C := hasLimitsOfSizeShrink.{0, 0, w, w} C
local instance chosenTensorLeftPreservesSmall (X : C) : PreservesColimitsOfSize.{0, 0} (tensorLeft X) := inferInstance
local instance chosenTensorRightPreservesSmall (X : C) : PreservesColimitsOfSize.{0, 0} (tensorRight X) := inferInstance
/-- The canonical Day structure on the original arbitrary R-module carrier. -/
local instance chosenCanonicalDayMonoidal : MonoidalCategory (DayFunctor I C) := inferInstance

variable (models : ChosenActionModels.{w} C) (small : PrettySmallSource.{w} C) (hm : HMonoidality C)
  (R : DayFunctor I C) [MonObj R]

local instance chosenModuleColimits : HasColimitsOfSize.{w, w} (CategoryTheory.Mod (DayFunctor I C) R) :=
    moduleHasColimits R
local instance chosenModuleSmallColimits : HasColimitsOfSize.{0, 0} (CategoryTheory.Mod (DayFunctor I C) R) :=
  hasColimitsOfSizeShrink.{0, 0, w, w} _
local instance chosenModuleFiniteColimits : HasFiniteColimits (CategoryTheory.Mod (DayFunctor I C) R) := inferInstance
local instance chosenModuleLimits : HasLimitsOfSize.{w, w} (CategoryTheory.Mod (DayFunctor I C) R) := moduleHasLimits R
local instance chosenModuleSmallLimits : HasLimitsOfSize.{0, 0} (CategoryTheory.Mod (DayFunctor I C) R) :=
  hasLimitsOfSizeShrink.{0, 0, w, w} _
local instance chosenModuleFiniteLimits : HasFiniteLimits (CategoryTheory.Mod (DayFunctor I C) R) := inferInstance

/-- The exact source-retained degree labels in the ordinary or positive model. -/
abbrev KeptDegree (positive : Bool) := {n : ℕ // positive = true → 0 < n}

/-- The original underlying base evaluations at precisely the retained degrees. -/
abbrev baseEvaluationFamily (positive : Bool) :
    KeptDegree positive → CategoryTheory.Mod (DayFunctor I C) R ⥤ C :=
  fun n => CategoryTheory.Mod.dayEvaluation R (card n.1)

/-- The actual weak class tested on those original retained R-module maps. -/
def levelWeak (positive : Bool) : MorphismProperty (CategoryTheory.Mod (DayFunctor I C) R) :=
  EvaluationTransfer.evaluationProperty (baseEvaluationFamily R positive) (weakEquivalences C)

omit [HasLimitsOfSize.{w, w} C] [IsLocallyPresentable.{w} C] in
/-- The original retained weak components preserve the exact n>0 or n>=0 source tests. -/
theorem levelWeak_iff (positive : Bool) {X Y : CategoryTheory.Mod (DayFunctor I C) R} (f : X ⟶ Y) :
    levelWeak R positive f ↔ ∀ n : ℕ, (positive = true → 0 < n) →
      weakEquivalences C ((CategoryTheory.Mod.dayEvaluation R (card n)).map f) := by
  rw [levelWeak, EvaluationTransfer.evaluationProperty_iff]
  exact ⟨fun h n hn => h ⟨n, hn⟩, fun h n => h n.1 n.2⟩

omit [HasLimitsOfSize.{w, w} C] [IsLocallyPresentable.{w} C] in
/-- The actual chosen weak equivalences are exactly the original underlying degree weak test. -/
theorem chosenWeak_iff (n : ℕ) {X Y : CategoryTheory.Mod (DayFunctor I C) R} (f : X ⟶ Y) :
    (models.model n).categoryWithWeakEquivalences.weakEquivalences ((degreeActionEvaluation R n).map f) ↔
      weakEquivalences C ((CategoryTheory.Mod.dayEvaluation R (card n)).map f) := by
  rw [models.weak_eq n]
  constructor
  · intro h
    exact h (SingleObj.star (Equiv.Perm (Fin n)))
  · intro h a
    exact h

omit [HasLimitsOfSize.{w, w} C] [IsLocallyPresentable.{w} C] in
/-- Both original free families have the exact chosen source right-class intersection. -/
theorem sourceRightClasses (positive : Bool) :
    (actionGenerators R positive models.I).rlp = (actionGenerators R positive models.J).rlp ⊓ levelWeak R positive := by
  ext X Y f
  rw [actionGenerators_rlp_iff, MorphismProperty.inf_iff, actionGenerators_rlp_iff, levelWeak_iff]
  constructor
  · intro hI
    refine ⟨?_, ?_⟩
    · intro n hn
      rw [models.J_rlp n]
      have hnI := hI n hn
      rw [models.I_rlp n] at hnI
      exact hnI.1
    · intro n hn
      have hnI := hI n hn
      rw [models.I_rlp n] at hnI
      exact (chosenWeak_iff models R n f).mp hnI.2
  · rintro ⟨hJ, hW⟩ n hn
    rw [models.I_rlp n]
    exact ⟨(models.J_rlp n) ▸ hJ n hn, (chosenWeak_iff models R n f).mpr (hW n hn)⟩

variable (e : ModuleGenerationRank models R)
local instance chosenSourceRankRegular : Fact e.cardinal.IsRegular := e.regular
/-- The actual ordinal bottom selected with the common source rank. -/
local instance chosenSourceRankBottom : OrderBot e.cardinal.ord.ToType := e.orderBot

include small hm e in
/-- Every actual original free J left-class map is weak at every retained degree, from the earned coefficient cells. -/
theorem generatedJ_weak (positive : Bool) :
    (actionGenerators R positive models.J).rlp.llp ≤ levelWeak R positive := by
  let _ : (actionGenerators R positive models.J).IsCardinalForSmallObjectArgument e.cardinal := e.J_eligible models R
      positive
  let _ : (couniversalWeakEquivalences C).IsStableUnderTransfiniteComposition.{w} := small.couniversal_transfinite
  let _ : (couniversalWeakEquivalences C).IsStableUnderCoproducts.{w} := isStableUnderCoproducts_of_cobase_transfinite _
  intro X Y f hf
  apply (levelWeak_iff R positive f).mpr
  intro m _
  let _ : PreservesColimitsOfSize.{w, w} (CategoryTheory.Mod.dayEvaluation R (card m)) :=
    moduleEvaluationPreservesColimits R _
  let _ : PreservesWellOrderContinuousOfShape e.cardinal.ord.ToType (CategoryTheory.Mod.dayEvaluation R (card m)) :=
    { preservesColimitsOfShape := fun _ _ => inferInstance }
  apply rlp_llp_le_inverseImage_of_cardinal_cells (actionGenerators R positive models.J)
    (weakEquivalences C) (CategoryTheory.Mod.dayEvaluation R (card m)) e.cardinal ?_ f hf
  intro U V k c
  apply couniversalWeakEquivalences_le_weakEquivalences
  apply c.map_mem_of_le (CategoryTheory.Mod.dayEvaluation R (card m))
    (actionGenerators R positive models.J) (couniversalWeakEquivalences C) ?_
  intro A B j hj
  obtain ⟨q⟩ := hj
  exact freeJ_evaluation_couniversal models small hm R q.1.1 m q.2.1.hom q.2.2

/-- The actual constructed ordinary or positive model on the original arbitrary R-module carrier. -/
@[instance_reducible]
def sourceModelCategory (positive : Bool) : ModelCategory (CategoryTheory.Mod (DayFunctor I C) R) := by
  let e := moduleGenerationRank models R
  let _ : Fact e.cardinal.IsRegular := e.regular
  let _ : OrderBot e.cardinal.ord.ToType := e.orderBot
  let _ : (actionGenerators R positive models.I).IsCardinalForSmallObjectArgument e.cardinal := e.I_eligible models R
      positive
  let _ : (actionGenerators R positive models.J).IsCardinalForSmallObjectArgument e.cardinal := e.J_eligible models R
      positive
  let _ : (actionGenerators R positive models.I).HasSmallObjectArgument.{w} := ⟨e.cardinal, inferInstance,
      inferInstance, inferInstance⟩
  let _ : (actionGenerators R positive models.J).HasSmallObjectArgument.{w} := ⟨e.cardinal, inferInstance,
      inferInstance, inferInstance⟩
  let _ : CategoryWithCofibrations (CategoryTheory.Mod (DayFunctor I C) R) := ⟨(actionGenerators R positive
      models.I).rlp.llp⟩
  let _ : CategoryWithFibrations (CategoryTheory.Mod (DayFunctor I C) R) := ⟨(actionGenerators R positive models.J).rlp⟩
  let _ : CategoryWithWeakEquivalences (CategoryTheory.Mod (DayFunctor I C) R) := ⟨levelWeak R positive⟩
  have hTwo : (levelWeak R positive).HasTwoOutOfThreeProperty :=
    EvaluationTransfer.evaluationProperty_hasTwoOutOfThree (baseEvaluationFamily R positive) (weakEquivalences C)
  let data := SmithModelStructureData.ofGenerators (actionGenerators R positive models.I)
    (actionGenerators R positive models.J) (levelWeak R positive) hTwo (sourceRightClasses models R positive)
    (generatedJ_weak models small hm R e positive)
  exact data.modelCategory hTwo rfl rfl rfl

end HomotopicalAlgebra.PositiveLevelModel.Chosen
