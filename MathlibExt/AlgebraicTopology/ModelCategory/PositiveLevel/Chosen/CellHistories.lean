/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.PositiveLevel.Chosen.FactorMaps
import MathlibExt.AlgebraicTopology.ModelCategory.PositiveLevel.Factorization.CellHistories

/-!
# Original chosen-action positive factors and their full actual cell histories

The cardinal is the source-produced common rank for both I and J domains and
codomains. The full cell histories have precisely the returned factor objects
and maps. Their original coproducts and attaching maps remain accessible, and
every original degree zero transition is an isomorphism.
-/

set_option autoImplicit false
noncomputable section
universe w v u

open CategoryTheory Limits MorphismProperty MonoidalCategory MonObj
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj MonoidalClosed

namespace HomotopicalAlgebra.PositiveLevelModel.Chosen

local notation "I" => CategoryTheory.Operad.SmallFinBijGroupoid

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [ModelCategory C] [HasColimitsOfSize.{w, w} C] [HasLimitsOfSize.{w, w} C]
  [IsLocallyPresentable.{w} C]

local instance historyChosenBaseSmallColimits : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink.{0, 0, w, w} C
local instance historyChosenBaseSmallLimits : HasLimitsOfSize.{0, 0} C := hasLimitsOfSizeShrink.{0, 0, w, w} C
/-- The canonical Day structure retained by the actual chosen cell histories. -/
local instance historyChosenDayMonoidal : MonoidalCategory (DayFunctor I C) := inferInstance

variable (models : ChosenActionModels.{w} C) (small : PrettySmallSource.{w} C) (hm : HMonoidality C)
  (R : DayFunctor I C) [MonObj R]

/-- The same actual source-produced common rank used in both returned factor values. -/
abbrev factorRank := moduleGenerationRank models R

local instance historyRankRegular : Fact (factorRank models R).cardinal.IsRegular := (factorRank models R).regular
/-- The original ordinal bottom used in both chosen factor histories. -/
local instance historyRankBottom : OrderBot (factorRank models R).cardinal.ord.ToType := (factorRank models R).orderBot
/-- The full original relative I-cell history ends in exactly the actual returned I left factor. -/
def positiveIHistory (f : Arrow (CategoryTheory.Mod (DayFunctor I C) R)) :
    RelativeCellComplex.{w}
      (fun (_ : (factorRank models R).cardinal.ord.ToType) => (actionGenerators R true models.I).homFamily)
      ((positiveCofibrantFactorizationData models small hm R).i.app f) :=
  by
    let _ : (actionGenerators R true models.I).IsCardinalForSmallObjectArgument (factorRank models R).cardinal :=
      (factorRank models R).I_eligible models R true
    exact SmallObject.relativeCellComplexιObj (actionGenerators R true models.I) (factorRank models R).cardinal f.hom

/-- The full original relative J-cell history ends in exactly the actual returned J left factor. -/
def positiveJHistory (f : Arrow (CategoryTheory.Mod (DayFunctor I C) R)) :
    RelativeCellComplex.{w}
      (fun (_ : (factorRank models R).cardinal.ord.ToType) => (actionGenerators R true models.J).homFamily)
      ((positiveFibrantFactorizationData models small hm R).i.app f) :=
  by
    let _ : (actionGenerators R true models.J).IsCardinalForSmallObjectArgument (factorRank models R).cardinal :=
      (factorRank models R).J_eligible models R true
    exact SmallObject.relativeCellComplexιObj (actionGenerators R true models.J) (factorRank models R).cardinal f.hom

/-- The actual returned I factor object is the original common-rank small object output. -/
theorem positiveIFactor_obj (f : Arrow (CategoryTheory.Mod (DayFunctor I C) R)) :
    let _ : (actionGenerators R true models.I).IsCardinalForSmallObjectArgument (factorRank models R).cardinal :=
      (factorRank models R).I_eligible models R true
    (positiveCofibrantFactorizationData models small hm R).Z.obj f =
      SmallObject.obj (actionGenerators R true models.I) (factorRank models R).cardinal f.hom := by
  let _ : (actionGenerators R true models.I).IsCardinalForSmallObjectArgument (factorRank models R).cardinal :=
    (factorRank models R).I_eligible models R true
  rfl

/-- The actual returned J factor object is the original common-rank small object output. -/
theorem positiveJFactor_obj (f : Arrow (CategoryTheory.Mod (DayFunctor I C) R)) :
    let _ : (actionGenerators R true models.J).IsCardinalForSmallObjectArgument (factorRank models R).cardinal :=
      (factorRank models R).J_eligible models R true
    (positiveFibrantFactorizationData models small hm R).Z.obj f =
      SmallObject.obj (actionGenerators R true models.J) (factorRank models R).cardinal f.hom := by
  let _ : (actionGenerators R true models.J).IsCardinalForSmallObjectArgument (factorRank models R).cardinal :=
    (factorRank models R).J_eligible models R true
  rfl

/-- The I intermediate map on every original caller square is the original whole small object map. -/
theorem positiveIFactor_map {f g : Arrow (CategoryTheory.Mod (DayFunctor I C) R)} (s : f ⟶ g) :
    let _ : (actionGenerators R true models.I).IsCardinalForSmallObjectArgument (factorRank models R).cardinal :=
      (factorRank models R).I_eligible models R true
    (positiveCofibrantFactorizationData models small hm R).Z.map s =
      SmallObject.objMap (actionGenerators R true models.I) (factorRank models R).cardinal s := by
  let _ : (actionGenerators R true models.I).IsCardinalForSmallObjectArgument (factorRank models R).cardinal :=
    (factorRank models R).I_eligible models R true
  rfl

/-- The J intermediate map on every original caller square retains the same original construction. -/
theorem positiveJFactor_map {f g : Arrow (CategoryTheory.Mod (DayFunctor I C) R)} (s : f ⟶ g) :
    let _ : (actionGenerators R true models.J).IsCardinalForSmallObjectArgument (factorRank models R).cardinal :=
      (factorRank models R).J_eligible models R true
    (positiveFibrantFactorizationData models small hm R).Z.map s =
      SmallObject.objMap (actionGenerators R true models.J) (factorRank models R).cardinal s := by
  let _ : (actionGenerators R true models.J).IsCardinalForSmallObjectArgument (factorRank models R).cardinal :=
    (factorRank models R).J_eligible models R true
  rfl

/-- Every original I successor retains its complete original coproduct and pushout attachment. -/
abbrev positiveIAttachment (f : Arrow (CategoryTheory.Mod (DayFunctor I C) R))
    (j : (factorRank models R).cardinal.ord.ToType) (hj : ¬ IsMax j) :=
  (positiveIHistory models small hm R f).attachCells j hj

/-- Every original J successor retains its complete original coproduct and pushout attachment. -/
abbrev positiveJAttachment (f : Arrow (CategoryTheory.Mod (DayFunctor I C) R))
    (j : (factorRank models R).cardinal.ord.ToType) (hj : ¬ IsMax j) :=
  (positiveJHistory models small hm R f).attachCells j hj

/-- The I cofan equation keeps the complete original positive free I arrow, without changing its label. -/
theorem positiveIAttachment_cofan_word (f : Arrow (CategoryTheory.Mod (DayFunctor I C) R))
    (j : (factorRank models R).cardinal.ord.ToType) (hj : ¬ IsMax j)
    (a : (positiveIAttachment models small hm R f j hj).ι) :
    (positiveIAttachment models small hm R f j hj).cofan₁.inj a ≫ (positiveIAttachment models small hm R f j hj).m =
      (actionGenerators R true models.I).homFamily ((positiveIAttachment models small hm R f j hj).π a) ≫
        (positiveIAttachment models small hm R f j hj).cofan₂.inj a :=
  (positiveIAttachment models small hm R f j hj).hm a

/-- The J cofan equation likewise retains every original positive free J arrow and original target injection. -/
theorem positiveJAttachment_cofan_word (f : Arrow (CategoryTheory.Mod (DayFunctor I C) R))
    (j : (factorRank models R).cardinal.ord.ToType) (hj : ¬ IsMax j)
    (a : (positiveJAttachment models small hm R f j hj).ι) :
    (positiveJAttachment models small hm R f j hj).cofan₁.inj a ≫ (positiveJAttachment models small hm R f j hj).m =
      (actionGenerators R true models.J).homFamily ((positiveJAttachment models small hm R f j hj).π a) ≫
        (positiveJAttachment models small hm R f j hj).cofan₂.inj a :=
  (positiveJAttachment models small hm R f j hj).hm a

local instance historyZeroColimits : PreservesColimitsOfSize.{w, w} (zeroEvaluation R) :=
  moduleEvaluationPreservesColimits R _
local instance historyZeroContinuous :
    PreservesWellOrderContinuousOfShape (factorRank models R).cardinal.ord.ToType (zeroEvaluation R) :=
  { preservesColimitsOfShape := fun _ _ => inferInstance }

/-- Every original I stage transition, including arbitrarily long ones, is isomorphic at degree zero. -/
theorem positiveIHistory_transition_zero_isIso
    (f : Arrow (CategoryTheory.Mod (DayFunctor I C) R))
    {a b : (factorRank models R).cardinal.ord.ToType} (s : a ⟶ b) :
    IsIso ((zeroEvaluation R).map ((positiveIHistory models small hm R f).F.map s)) :=
  by
    let _ : (actionGenerators R true models.I).IsCardinalForSmallObjectArgument (factorRank models R).cardinal :=
      (factorRank models R).I_eligible models R true
    exact ActualSourceCells.mapped_transition_isIso (actionGenerators R true models.I) (factorRank models R).cardinal
      (zeroEvaluation R) (actionPositiveGenerators_le_zeroIsomorphisms R models.I) f s

/-- Every original J stage transition retains the same unrestricted degree zero isomorphism rule. -/
theorem positiveJHistory_transition_zero_isIso
    (f : Arrow (CategoryTheory.Mod (DayFunctor I C) R))
    {a b : (factorRank models R).cardinal.ord.ToType} (s : a ⟶ b) :
    IsIso ((zeroEvaluation R).map ((positiveJHistory models small hm R f).F.map s)) :=
  by
    let _ : (actionGenerators R true models.J).IsCardinalForSmallObjectArgument (factorRank models R).cardinal :=
      (factorRank models R).J_eligible models R true
    exact ActualSourceCells.mapped_transition_isIso (actionGenerators R true models.J) (factorRank models R).cardinal
      (zeroEvaluation R) (actionPositiveGenerators_le_zeroIsomorphisms R models.J) f s

end HomotopicalAlgebra.PositiveLevelModel.Chosen
