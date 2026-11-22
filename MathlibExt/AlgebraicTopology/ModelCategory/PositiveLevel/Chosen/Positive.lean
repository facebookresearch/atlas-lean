/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.PositiveLevel.Chosen.Model

/-!
# All classes and actual factors of the original chosen action models

Both ordinary and positive dictionaries are constructed on the same original
R-module category. Fibrations retain the given genuine finite-action model
tests. Omitting degree zero gives exactly the ordinary cofibrations with an
isomorphic original zero component, through the actual positive I argument.
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

local instance positiveChosenBaseSmallColimits : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink.{0, 0, w, w} C
local instance positiveChosenBaseSmallLimits : HasLimitsOfSize.{0, 0} C := hasLimitsOfSizeShrink.{0, 0, w, w} C
local instance positiveChosenTensorLeftPreserves (X : C) : PreservesColimitsOfSize.{0, 0} (tensorLeft X) :=
    inferInstance
local instance positiveChosenTensorRightPreserves (X : C) : PreservesColimitsOfSize.{0, 0} (tensorRight X) :=
    inferInstance
/-- The same canonical Day structure for the ordinary and positive models. -/
local instance positiveChosenDayMonoidal : MonoidalCategory (DayFunctor I C) := inferInstance

variable (models : ChosenActionModels.{w} C) (small : PrettySmallSource.{w} C) (hm : HMonoidality C)
  (R : DayFunctor I C) [MonObj R]

/-- The actual constructed ordinary model on the same original R-module carrier. -/
@[instance_reducible]
def ordinaryModelCategory : ModelCategory (CategoryTheory.Mod (DayFunctor I C) R) :=
  sourceModelCategory models small hm R false

/-- The actual constructed positive model on the unchanged original R-module carrier. -/
@[instance_reducible]
def positiveModelCategory : ModelCategory (CategoryTheory.Mod (DayFunctor I C) R) :=
  sourceModelCategory models small hm R true

/-- The complete original chosen-action fibration class, at exactly the retained degree labels. -/
def levelFibrations (positive : Bool) : MorphismProperty (CategoryTheory.Mod (DayFunctor I C) R) :=
  fun _ _ f => ∀ n : ℕ, (positive = true → 0 < n) →
    (models.model n).categoryWithFibrations.fibrations ((degreeActionEvaluation R n).map f)

include small hm in
/-- The actual returned weak class is precisely the original retained underlying degree weak class. -/
theorem source_weakEquivalences_eq (positive : Bool) :
    let _ : ModelCategory (CategoryTheory.Mod (DayFunctor I C) R) := sourceModelCategory models small hm R positive
    weakEquivalences (CategoryTheory.Mod (DayFunctor I C) R) = levelWeak R positive := rfl

include small hm in
/-- The actual cofibrations use every and only the original retained chosen free I maps. -/
theorem source_cofibrations_eq (positive : Bool) :
    let _ : ModelCategory (CategoryTheory.Mod (DayFunctor I C) R) := sourceModelCategory models small hm R positive
    cofibrations (CategoryTheory.Mod (DayFunctor I C) R) = (actionGenerators R positive models.I).rlp.llp := rfl

include small hm in
/-- The actual chosen fibrations are tested at the retained degrees, with the complete original actions. -/
theorem source_fibrations_eq (positive : Bool) :
    let _ : ModelCategory (CategoryTheory.Mod (DayFunctor I C) R) := sourceModelCategory models small hm R positive
    fibrations (CategoryTheory.Mod (DayFunctor I C) R) = levelFibrations models R positive := by
  change (actionGenerators R positive models.J).rlp = _
  ext X Y f
  rw [actionGenerators_rlp_iff]
  exact forall_congr' (fun n => forall_congr' (fun _ => by rw [models.J_rlp n]))

include small hm in
/-- The actual full trivial-fibration class is exactly the right class of the original free I family. -/
theorem source_trivialFibrations_eq (positive : Bool) :
    let _ : ModelCategory (CategoryTheory.Mod (DayFunctor I C) R) := sourceModelCategory models small hm R positive
    trivialFibrations (CategoryTheory.Mod (DayFunctor I C) R) = (actionGenerators R positive models.I).rlp :=
  (sourceRightClasses models R positive).symm

include small hm in
/-- The actual full trivial-cofibration class is the original free J generated left class. -/
theorem source_trivialCofibrations_eq (positive : Bool) :
    let _ : ModelCategory (CategoryTheory.Mod (DayFunctor I C) R) := sourceModelCategory models small hm R positive
    trivialCofibrations (CategoryTheory.Mod (DayFunctor I C) R) = (actionGenerators R positive models.J).rlp.llp := by
  let _ : ModelCategory (CategoryTheory.Mod (DayFunctor I C) R) := sourceModelCategory models small hm R positive
  change trivialCofibrations (CategoryTheory.Mod (DayFunctor I C) R) = _
  rw [← fibrations_llp (CategoryTheory.Mod (DayFunctor I C) R)]
  rfl

/-- The actual common-rank I small object factorization, without replacing any factor map. -/
def sourceCofibrantFactorizationData (positive : Bool) :
    let _ : ModelCategory (CategoryTheory.Mod (DayFunctor I C) R) := sourceModelCategory models small hm R positive
    FunctorialFactorizationData (cofibrations (CategoryTheory.Mod (DayFunctor I C) R))
      (trivialFibrations (CategoryTheory.Mod (DayFunctor I C) R)) := by
  let _ : ModelCategory (CategoryTheory.Mod (DayFunctor I C) R) := sourceModelCategory models small hm R positive
  let e := moduleGenerationRank models R
  let _ : Fact e.cardinal.IsRegular := e.regular
  let _ : OrderBot e.cardinal.ord.ToType := e.orderBot
  let _ : (actionGenerators R positive models.I).IsCardinalForSmallObjectArgument e.cardinal :=
    e.I_eligible models R positive
  exact (SmallObject.functorialFactorizationData (actionGenerators R positive models.I) e.cardinal).ofLE
    le_rfl (source_trivialFibrations_eq models small hm R positive).symm.le

/-- The actual common-rank J small object factorization retains its original complete values. -/
def sourceFibrantFactorizationData (positive : Bool) :
    let _ : ModelCategory (CategoryTheory.Mod (DayFunctor I C) R) := sourceModelCategory models small hm R positive
    FunctorialFactorizationData (trivialCofibrations (CategoryTheory.Mod (DayFunctor I C) R))
      (fibrations (CategoryTheory.Mod (DayFunctor I C) R)) := by
  let _ : ModelCategory (CategoryTheory.Mod (DayFunctor I C) R) := sourceModelCategory models small hm R positive
  let e := moduleGenerationRank models R
  let _ : Fact e.cardinal.IsRegular := e.regular
  let _ : OrderBot e.cardinal.ord.ToType := e.orderBot
  let _ : (actionGenerators R positive models.J).IsCardinalForSmallObjectArgument e.cardinal :=
    e.J_eligible models R positive
  exact (SmallObject.functorialFactorizationData (actionGenerators R positive models.J) e.cardinal).ofLE
    (source_trivialCofibrations_eq models small hm R positive).symm.le le_rfl

/-- The complete original positive free I factor value at the actual source rank. -/
abbrev positiveCofibrantFactorizationData := sourceCofibrantFactorizationData models small hm R true

/-- The complete original positive free J factor value at that same source rank. -/
abbrev positiveFibrantFactorizationData := sourceFibrantFactorizationData models small hm R true

/-- Positive cofibrations equal the actual ordinary model cofibrations with original degree zero isomorphic. -/
theorem positive_cofibrations_eq_ordinary_zero :
    let _ : ModelCategory (CategoryTheory.Mod (DayFunctor I C) R) := positiveModelCategory models small hm R
    cofibrations (CategoryTheory.Mod (DayFunctor I C) R) =
      (ordinaryModelCategory models small hm R).categoryWithCofibrations.cofibrations ⊓ zeroIsomorphisms R := by
  let e := moduleGenerationRank models R
  let _ : Fact e.cardinal.IsRegular := e.regular
  let _ : OrderBot e.cardinal.ord.ToType := e.orderBot
  let _ : (actionGenerators R true models.I).IsCardinalForSmallObjectArgument e.cardinal :=
    e.I_eligible models R true
  let _ : PreservesColimitsOfSize.{w, w} (zeroEvaluation R) := moduleEvaluationPreservesColimits R _
  let _ : PreservesWellOrderContinuousOfShape e.cardinal.ord.ToType (zeroEvaluation R) :=
    { preservesColimitsOfShape := fun _ _ => inferInstance }
  change (actionGenerators R true models.I).rlp.llp =
    (actionGenerators R false models.I).rlp.llp ⊓ zeroIsomorphisms R
  exact restrictedGeneratedLeft_eq
    (actionGenerators R true models.I) (actionGenerators R false models.I) (zeroEvaluation R) e.cardinal
    (actionPositiveGenerators_le_ordinary R models.I) (actionPositiveGenerators_le_zeroIsomorphisms R models.I)
    (actionPositiveRight_zero_le_ordinaryRight R models.I)

include small hm in
/-- Every retained original finite-action free/evaluation adjunction is Quillen for the constructed model. -/
theorem source_freeEvaluation_isQuillenAdjunction (positive : Bool) (n : ℕ)
    (hn : positive = true → 0 < n) :
    let _ : ModelCategory (CategoryTheory.Mod (DayFunctor I C) R) := sourceModelCategory models small hm R positive
    let _ : ModelCategory (degreeActionCategory (C := C) n) := models.model n
    (degreeActionAdjunction R n).IsQuillenAdjunction := by
  let _ : ModelCategory (CategoryTheory.Mod (DayFunctor I C) R) := sourceModelCategory models small hm R positive
  let _ : ModelCategory (degreeActionCategory (C := C) n) := models.model n
  apply Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations
  · intro X Y f hf
    exact (actionGenerators_rlp_iff R positive models.J f).mp hf n hn |> (models.J_rlp n).le _
  · intro X Y f hf
    have hi := (source_trivialFibrations_eq models small hm R positive).le f hf
    exact (actionGenerators_rlp_iff R positive models.I f).mp hi n hn |> (models.I_rlp n).le _

/-- Every strictly positive degree retains its full original finite-action Quillen assertion. -/
theorem positive_freeEvaluation_isQuillenAdjunction (n : ℕ) (hn : 0 < n) :
    let _ : ModelCategory (CategoryTheory.Mod (DayFunctor I C) R) := positiveModelCategory models small hm R
    let _ : ModelCategory (degreeActionCategory (C := C) n) := models.model n
    (degreeActionAdjunction R n).IsQuillenAdjunction :=
  source_freeEvaluation_isQuillenAdjunction models small hm R true n (fun _ => hn)

end HomotopicalAlgebra.PositiveLevelModel.Chosen
