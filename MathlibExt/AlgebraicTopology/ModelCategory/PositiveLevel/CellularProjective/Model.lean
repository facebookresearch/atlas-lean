/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.PositiveLevel.CellularProjective.Generators
public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenAdjunction

/-!
# Actual projective level R-module models from cellular source data

The existing R-module carrier, original base I/J maps, and the actual produced
source rank give both full small-object arguments. Their original free/evaluation
right classes and the earned R-coefficient cell acyclicity construct the model.
All five classes and both actual functorial factor values are retained.
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

local instance modelBaseSmallColimits : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink.{0, 0, w, w} C

variable (R : DayFunctor I C) [MonObj R]
  (hR : ∀ n : ℕ, IsCofibrant (R.functor.obj (CategoryTheory.Operad.SmallFinBijGroupoid.card n)))

local instance modelModuleColimits : HasColimitsOfSize.{w, w} (CategoryTheory.Mod (DayFunctor I C) R) :=
  moduleHasColimits R
local instance modelModuleSmallColimits : HasColimitsOfSize.{0, 0} (CategoryTheory.Mod (DayFunctor I C) R) :=
  hasColimitsOfSizeShrink.{0, 0, w, w} _
local instance modelModuleFiniteColimits : HasFiniteColimits (CategoryTheory.Mod (DayFunctor I C) R) := inferInstance
local instance modelModuleSmallLimits : HasLimitsOfSize.{0, 0} (CategoryTheory.Mod (DayFunctor I C) R) :=
  moduleHasLimits.{0} R
local instance modelModuleFiniteLimits : HasFiniteLimits (CategoryTheory.Mod (DayFunctor I C) R) := inferInstance

variable {S : Type} [Small.{w} S] (degree : S → ℕ)

omit [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [IsClosedSymmetricMonoidalModelCategory C] [HasColimitsOfSize.{w, w} C]
  [HasLimitsOfSize.{0, 0} C] [LocallySmall.{w} C] [Small.{w} S] in
/-- The same actual base right-class intersection, before the module transfer. -/
theorem baseRightClasses : d.I.rlp = d.J.rlp ⊓ weakEquivalences C := by
  rw [d.I_rlp, d.J_rlp]
  rfl

/-- The actual constructed level model on the existing R-module carrier at exactly the retained degrees. -/
@[instance_reducible]
def sourceModelCategory : ModelCategory (CategoryTheory.Mod (DayFunctor I C) R) := by
  let e := cellularModuleGenerationRank d h
  let _ : Fact e.cardinal.IsRegular := e.regular
  let _ : OrderBot e.cardinal.ord.ToType := e.orderBot
  let _ : (adjointFamilyGenerators (projectiveFreeFamily R degree) d.I).IsCardinalForSmallObjectArgument e.cardinal :=
    projectiveI_eligible d h R hR degree e
  let _ : (adjointFamilyGenerators (projectiveFreeFamily R degree) d.J).IsCardinalForSmallObjectArgument e.cardinal :=
    projectiveJ_eligible d h R hR degree e
  let _ : (adjointFamilyGenerators (projectiveFreeFamily R degree) d.I).HasSmallObjectArgument.{w} :=
    ⟨e.cardinal, inferInstance, inferInstance, inferInstance⟩
  let _ : (adjointFamilyGenerators (projectiveFreeFamily R degree) d.J).HasSmallObjectArgument.{w} :=
    ⟨e.cardinal, inferInstance, inferInstance, inferInstance⟩
  exact EvaluationTransfer.evaluationProjectiveModelCategory
    (projectiveFreeFamily R degree) (projectiveEvaluationFamily R degree) (projectiveAdjunctionFamily R degree)
    d.I d.J (weakEquivalences C) (baseRightClasses d)
    (projectiveJ_generatedLeft_weak d h R hR degree e)

include hR h in
/-- The actual returned weak class is exactly the original evaluations at the retained degrees. -/
theorem source_weakEquivalences_eq :
    let _ : ModelCategory (CategoryTheory.Mod (DayFunctor I C) R) := sourceModelCategory d h R hR degree
    weakEquivalences (CategoryTheory.Mod (DayFunctor I C) R) =
      EvaluationTransfer.evaluationProperty (projectiveEvaluationFamily R degree) (weakEquivalences C) := rfl

include hR h in
/-- The complete returned cofibration class uses the very same original free I maps. -/
theorem source_cofibrations_eq :
    let _ : ModelCategory (CategoryTheory.Mod (DayFunctor I C) R) := sourceModelCategory d h R hR degree
    cofibrations (CategoryTheory.Mod (DayFunctor I C) R) =
      (adjointFamilyGenerators (projectiveFreeFamily R degree) d.I).rlp.llp := rfl

include hR h in
/-- The returned fibrations are the original base fibrations at those actual evaluation components. -/
theorem source_fibrations_eq :
    let _ : ModelCategory (CategoryTheory.Mod (DayFunctor I C) R) := sourceModelCategory d h R hR degree
    fibrations (CategoryTheory.Mod (DayFunctor I C) R) =
      EvaluationTransfer.evaluationProperty (projectiveEvaluationFamily R degree) (fibrations C) := by
  change (adjointFamilyGenerators (projectiveFreeFamily R degree) d.J).rlp = _
  rw [EvaluationTransfer.evaluatedGenerators_rlp_eq
    (projectiveFreeFamily R degree) (projectiveEvaluationFamily R degree) (projectiveAdjunctionFamily R degree),
        d.J_rlp]

include hR h in
/-- The returned trivial fibrations preserve the full original base intersection at every retained degree. -/
theorem source_trivialFibrations_eq :
    let _ : ModelCategory (CategoryTheory.Mod (DayFunctor I C) R) := sourceModelCategory d h R hR degree
    trivialFibrations (CategoryTheory.Mod (DayFunctor I C) R) =
      EvaluationTransfer.evaluationProperty (projectiveEvaluationFamily R degree) (trivialFibrations C) := by
  let _ : ModelCategory (CategoryTheory.Mod (DayFunctor I C) R) := sourceModelCategory d h R hR degree
  change fibrations (CategoryTheory.Mod (DayFunctor I C) R) ⊓ weakEquivalences (CategoryTheory.Mod (DayFunctor I C) R) =
      _
  rw [source_fibrations_eq d h R hR degree, source_weakEquivalences_eq d h R hR degree]
  exact (EvaluationTransfer.evaluationProperty_inf _ (fibrations C) (weakEquivalences C)).symm

include hR h in
/-- The returned trivial cofibrations are the full left class generated by the original free J arrows. -/
theorem source_trivialCofibrations_eq :
    let _ : ModelCategory (CategoryTheory.Mod (DayFunctor I C) R) := sourceModelCategory d h R hR degree
    trivialCofibrations (CategoryTheory.Mod (DayFunctor I C) R) =
      (adjointFamilyGenerators (projectiveFreeFamily R degree) d.J).rlp.llp := by
  let _ : ModelCategory (CategoryTheory.Mod (DayFunctor I C) R) := sourceModelCategory d h R hR degree
  change trivialCofibrations (CategoryTheory.Mod (DayFunctor I C) R) =
    (adjointFamilyGenerators (projectiveFreeFamily R degree) d.J).rlp.llp
  rw [← fibrations_llp (CategoryTheory.Mod (DayFunctor I C) R)]
  rfl

/-- The actual constructed free-I factorization value uses the source rank and unchanged original carrier maps. -/
def sourceCofibrantFactorizationData :
    let _ : ModelCategory (CategoryTheory.Mod (DayFunctor I C) R) := sourceModelCategory d h R hR degree
    FunctorialFactorizationData (cofibrations (CategoryTheory.Mod (DayFunctor I C) R))
      (trivialFibrations (CategoryTheory.Mod (DayFunctor I C) R)) := by
  let _ : ModelCategory (CategoryTheory.Mod (DayFunctor I C) R) := sourceModelCategory d h R hR degree
  let e := cellularModuleGenerationRank d h
  let _ : Fact e.cardinal.IsRegular := e.regular
  let _ : OrderBot e.cardinal.ord.ToType := e.orderBot
  let _ : (adjointFamilyGenerators (projectiveFreeFamily R degree) d.I).IsCardinalForSmallObjectArgument e.cardinal :=
    projectiveI_eligible d h R hR degree e
  have hRight : (adjointFamilyGenerators (projectiveFreeFamily R degree) d.I).rlp =
      trivialFibrations (CategoryTheory.Mod (DayFunctor I C) R) := by
    rw [source_trivialFibrations_eq d h R hR degree,
      EvaluationTransfer.evaluatedGenerators_rlp_eq
        (projectiveFreeFamily R degree) (projectiveEvaluationFamily R degree) (projectiveAdjunctionFamily R degree),
            d.I_rlp]
  exact (SmallObject.functorialFactorizationData (adjointFamilyGenerators (projectiveFreeFamily R degree) d.I)
    e.cardinal).ofLE le_rfl hRight.le

/-- The actual constructed free-J factorization is the same original source-rank small-object construction. -/
def sourceFibrantFactorizationData :
    let _ : ModelCategory (CategoryTheory.Mod (DayFunctor I C) R) := sourceModelCategory d h R hR degree
    FunctorialFactorizationData (trivialCofibrations (CategoryTheory.Mod (DayFunctor I C) R))
      (fibrations (CategoryTheory.Mod (DayFunctor I C) R)) := by
  let _ : ModelCategory (CategoryTheory.Mod (DayFunctor I C) R) := sourceModelCategory d h R hR degree
  let e := cellularModuleGenerationRank d h
  let _ : Fact e.cardinal.IsRegular := e.regular
  let _ : OrderBot e.cardinal.ord.ToType := e.orderBot
  let _ : (adjointFamilyGenerators (projectiveFreeFamily R degree) d.J).IsCardinalForSmallObjectArgument e.cardinal :=
    projectiveJ_eligible d h R hR degree e
  exact (SmallObject.functorialFactorizationData (adjointFamilyGenerators (projectiveFreeFamily R degree) d.J)
    e.cardinal).ofLE (source_trivialCofibrations_eq d h R hR degree).symm.le le_rfl

include hR h in
/-- Every retained original free/evaluation adjunction is Quillen for the actual constructed source model. -/
theorem source_freeEvaluation_isQuillenAdjunction (s : S) :
    let _ : ModelCategory (CategoryTheory.Mod (DayFunctor I C) R) := sourceModelCategory d h R hR degree
    (projectiveAdjunctionFamily R degree s).IsQuillenAdjunction := by
  let _ : ModelCategory (CategoryTheory.Mod (DayFunctor I C) R) := sourceModelCategory d h R hR degree
  apply Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations
  · intro X Y f hf
    rw [source_fibrations_eq d h R hR degree] at hf
    exact (EvaluationTransfer.evaluationProperty_iff _ _ f).mp hf s
  · intro X Y f hf
    rw [source_trivialFibrations_eq d h R hR degree] at hf
    exact (EvaluationTransfer.evaluationProperty_iff _ _ f).mp hf s

end HomotopicalAlgebra.PositiveLevelModel.CellularProjective
