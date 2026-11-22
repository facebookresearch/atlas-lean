/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.PositiveLevel.CellularProjective.FactorMaps
public import MathlibExt.AlgebraicTopology.ModelCategory.PositiveLevel.Factorization.CellHistories

/-!
# Original projective positive factors and their full actual cell histories

The cardinal is the source-produced common rank for both I and J domains and
codomains. The full cell histories have precisely the returned factor objects
and maps. Their original coproducts and attaching maps remain accessible, and
every original degree zero transition is an isomorphism.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe w v u

open CategoryTheory Limits MorphismProperty MonoidalCategory MonObj
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj MonoidalClosed

namespace HomotopicalAlgebra.PositiveLevelModel.CellularProjective

local notation "I" => CategoryTheory.Operad.SmallFinBijGroupoid

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [ModelCategory C] [IsClosedSymmetricMonoidalModelCategory C]
  [HasColimitsOfSize.{w, w} C] [HasLimitsOfSize.{0, 0} C] [LocallySmall.{w} C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ) (h : CellularSource d)

local instance historyBaseSmallColimits : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink.{0, 0, w, w} C
/-- The canonical Day tensor structure on the original coefficient category. -/
local instance historyDayMonoidal : MonoidalCategory (DayFunctor I C) := inferInstance

variable (R : DayFunctor I C) [MonObj R]
  (hR : ∀ n : ℕ, IsCofibrant (R.functor.obj (CategoryTheory.Operad.SmallFinBijGroupoid.card n)))

/-- The same actual source-produced common rank used in both returned factor values. -/
abbrev factorRank := cellularModuleGenerationRank d h

local instance historyRankRegular : Fact (factorRank d h).cardinal.IsRegular := (factorRank d h).regular
/-- The actual ordinal bottom used by both original factor histories. -/
local instance historyRankBottom : OrderBot (factorRank d h).cardinal.ord.ToType := (factorRank d h).orderBot
/-- The full original relative I-cell history ends in exactly the actual returned I left factor. -/
def positiveIHistory (f : Arrow (CategoryTheory.Mod (DayFunctor I C) R)) :
    RelativeCellComplex.{w}
      (fun (_ : (factorRank d h).cardinal.ord.ToType) => (positiveGenerators R d.I).homFamily)
      ((positiveCofibrantFactorizationData d h R hR).i.app f) :=
  by
    let _ : (positiveGenerators R d.I).IsCardinalForSmallObjectArgument (factorRank d h).cardinal :=
      projectiveI_eligible d h R hR (fun n : ℕ+ => n) (factorRank d h)
    exact SmallObject.relativeCellComplexιObj (positiveGenerators R d.I) (factorRank d h).cardinal f.hom

/-- The full original relative J-cell history ends in exactly the actual returned J left factor. -/
def positiveJHistory (f : Arrow (CategoryTheory.Mod (DayFunctor I C) R)) :
    RelativeCellComplex.{w}
      (fun (_ : (factorRank d h).cardinal.ord.ToType) => (positiveGenerators R d.J).homFamily)
      ((positiveFibrantFactorizationData d h R hR).i.app f) :=
  by
    let _ : (positiveGenerators R d.J).IsCardinalForSmallObjectArgument (factorRank d h).cardinal :=
      projectiveJ_eligible d h R hR (fun n : ℕ+ => n) (factorRank d h)
    exact SmallObject.relativeCellComplexιObj (positiveGenerators R d.J) (factorRank d h).cardinal f.hom

/-- The actual returned I factor object is the original common-rank small object output. -/
theorem positiveIFactor_obj (f : Arrow (CategoryTheory.Mod (DayFunctor I C) R)) :
    let _ : (positiveGenerators R d.I).IsCardinalForSmallObjectArgument (factorRank d h).cardinal :=
      projectiveI_eligible d h R hR (fun n : ℕ+ => n) (factorRank d h)
    (positiveCofibrantFactorizationData d h R hR).Z.obj f =
      SmallObject.obj (positiveGenerators R d.I) (factorRank d h).cardinal f.hom := by
  let _ : (positiveGenerators R d.I).IsCardinalForSmallObjectArgument (factorRank d h).cardinal :=
    projectiveI_eligible d h R hR (fun n : ℕ+ => n) (factorRank d h)
  rfl

/-- The actual returned J factor object is the original common-rank small object output. -/
theorem positiveJFactor_obj (f : Arrow (CategoryTheory.Mod (DayFunctor I C) R)) :
    let _ : (positiveGenerators R d.J).IsCardinalForSmallObjectArgument (factorRank d h).cardinal :=
      projectiveJ_eligible d h R hR (fun n : ℕ+ => n) (factorRank d h)
    (positiveFibrantFactorizationData d h R hR).Z.obj f =
      SmallObject.obj (positiveGenerators R d.J) (factorRank d h).cardinal f.hom := by
  let _ : (positiveGenerators R d.J).IsCardinalForSmallObjectArgument (factorRank d h).cardinal :=
    projectiveJ_eligible d h R hR (fun n : ℕ+ => n) (factorRank d h)
  rfl

/-- The I intermediate map on every original caller square is the original whole small object map. -/
theorem positiveIFactor_map {f g : Arrow (CategoryTheory.Mod (DayFunctor I C) R)} (s : f ⟶ g) :
    let _ : (positiveGenerators R d.I).IsCardinalForSmallObjectArgument (factorRank d h).cardinal :=
      projectiveI_eligible d h R hR (fun n : ℕ+ => n) (factorRank d h)
    (positiveCofibrantFactorizationData d h R hR).Z.map s =
      SmallObject.objMap (positiveGenerators R d.I) (factorRank d h).cardinal s := by
  let _ : (positiveGenerators R d.I).IsCardinalForSmallObjectArgument (factorRank d h).cardinal :=
    projectiveI_eligible d h R hR (fun n : ℕ+ => n) (factorRank d h)
  rfl

/-- The J intermediate map on every original caller square retains the same original construction. -/
theorem positiveJFactor_map {f g : Arrow (CategoryTheory.Mod (DayFunctor I C) R)} (s : f ⟶ g) :
    let _ : (positiveGenerators R d.J).IsCardinalForSmallObjectArgument (factorRank d h).cardinal :=
      projectiveJ_eligible d h R hR (fun n : ℕ+ => n) (factorRank d h)
    (positiveFibrantFactorizationData d h R hR).Z.map s =
      SmallObject.objMap (positiveGenerators R d.J) (factorRank d h).cardinal s := by
  let _ : (positiveGenerators R d.J).IsCardinalForSmallObjectArgument (factorRank d h).cardinal :=
    projectiveJ_eligible d h R hR (fun n : ℕ+ => n) (factorRank d h)
  rfl

/-- Every original I successor retains its complete original coproduct and pushout attachment. -/
abbrev positiveIAttachment (f : Arrow (CategoryTheory.Mod (DayFunctor I C) R))
    (j : (factorRank d h).cardinal.ord.ToType) (hj : ¬ IsMax j) :=
  (positiveIHistory d h R hR f).attachCells j hj

/-- Every original J successor retains its complete original coproduct and pushout attachment. -/
abbrev positiveJAttachment (f : Arrow (CategoryTheory.Mod (DayFunctor I C) R))
    (j : (factorRank d h).cardinal.ord.ToType) (hj : ¬ IsMax j) :=
  (positiveJHistory d h R hR f).attachCells j hj

/-- The I cofan equation keeps the complete original positive free I arrow, without changing its label. -/
theorem positiveIAttachment_cofan_word (f : Arrow (CategoryTheory.Mod (DayFunctor I C) R))
    (j : (factorRank d h).cardinal.ord.ToType) (hj : ¬ IsMax j)
    (a : (positiveIAttachment d h R hR f j hj).ι) :
    (positiveIAttachment d h R hR f j hj).cofan₁.inj a ≫ (positiveIAttachment d h R hR f j hj).m =
      (positiveGenerators R d.I).homFamily ((positiveIAttachment d h R hR f j hj).π a) ≫
        (positiveIAttachment d h R hR f j hj).cofan₂.inj a :=
  (positiveIAttachment d h R hR f j hj).hm a

/-- The J cofan equation likewise retains every original positive free J arrow and original target injection. -/
theorem positiveJAttachment_cofan_word (f : Arrow (CategoryTheory.Mod (DayFunctor I C) R))
    (j : (factorRank d h).cardinal.ord.ToType) (hj : ¬ IsMax j)
    (a : (positiveJAttachment d h R hR f j hj).ι) :
    (positiveJAttachment d h R hR f j hj).cofan₁.inj a ≫ (positiveJAttachment d h R hR f j hj).m =
      (positiveGenerators R d.J).homFamily ((positiveJAttachment d h R hR f j hj).π a) ≫
        (positiveJAttachment d h R hR f j hj).cofan₂.inj a :=
  (positiveJAttachment d h R hR f j hj).hm a

local instance historyZeroColimits : PreservesColimitsOfSize.{w, w} (zeroEvaluation R) :=
  moduleEvaluationPreservesColimits R _
local instance historyZeroContinuous :
    PreservesWellOrderContinuousOfShape (factorRank d h).cardinal.ord.ToType (zeroEvaluation R) :=
  { preservesColimitsOfShape := fun _ _ => inferInstance }

/-- Every original I stage transition, including arbitrarily long ones, is isomorphic at degree zero. -/
theorem positiveIHistory_transition_zero_isIso
    (f : Arrow (CategoryTheory.Mod (DayFunctor I C) R))
    {a b : (factorRank d h).cardinal.ord.ToType} (s : a ⟶ b) :
    IsIso ((zeroEvaluation R).map ((positiveIHistory d h R hR f).F.map s)) :=
  by
    let _ : (positiveGenerators R d.I).IsCardinalForSmallObjectArgument (factorRank d h).cardinal :=
      projectiveI_eligible d h R hR (fun n : ℕ+ => n) (factorRank d h)
    exact ActualSourceCells.mapped_transition_isIso (positiveGenerators R d.I) (factorRank d h).cardinal
      (zeroEvaluation R) (positiveGenerators_le_zeroIsomorphisms R d.I) f s

/-- Every original J stage transition retains the same unrestricted degree zero isomorphism rule. -/
theorem positiveJHistory_transition_zero_isIso
    (f : Arrow (CategoryTheory.Mod (DayFunctor I C) R))
    {a b : (factorRank d h).cardinal.ord.ToType} (s : a ⟶ b) :
    IsIso ((zeroEvaluation R).map ((positiveJHistory d h R hR f).F.map s)) :=
  by
    let _ : (positiveGenerators R d.J).IsCardinalForSmallObjectArgument (factorRank d h).cardinal :=
      projectiveJ_eligible d h R hR (fun n : ℕ+ => n) (factorRank d h)
    exact ActualSourceCells.mapped_transition_isIso (positiveGenerators R d.J) (factorRank d h).cardinal
      (zeroEvaluation R) (positiveGenerators_le_zeroIsomorphisms R d.J) f s

end HomotopicalAlgebra.PositiveLevelModel.CellularProjective
