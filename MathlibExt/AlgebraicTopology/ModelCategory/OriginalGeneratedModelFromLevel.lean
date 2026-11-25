/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.OriginalGeneratedModel

/-!
# Keep an existing level-classified I record in two-family model assembly

The input I record is already classified in the actual existing level model.
Equality of its cofibration class with the original I-left class derives the
corresponding trivial-fibration equality. Reclassification then retains that
same complete given record. The constructed model, both model-keyed carriers
and all replacement maps use this value; no new small-object construction is
chosen.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty

namespace HomotopicalAlgebra.OriginalGeneratedModel

variable {C : Type u} [Category.{v} C]

/-- The existing level model's actual cofibrations determine its complete right class. -/
theorem level_trivialFibrations_eq (level : ModelCategory C) (I : MorphismProperty C)
    (hCof : level.categoryWithCofibrations.cofibrations = I.rlp.llp) :
    level.categoryWithFibrations.fibrations ⊓
        level.categoryWithWeakEquivalences.weakEquivalences = I.rlp := by
  let : ModelCategory C := level
  calc
    level.categoryWithFibrations.fibrations ⊓
        level.categoryWithWeakEquivalences.weakEquivalences =
        level.categoryWithCofibrations.cofibrations.rlp := (cofibrations_rlp C).symm
    _ = I.rlp.llp.rlp := congrArg MorphismProperty.rlp hCof
    _ = I.rlp := I.rlp_llp_rlp

/-- Reclassify the original level I record without replacing any middle object or map. -/
def originalIFromLevel (level : ModelCategory C) (I : MorphismProperty C)
    (hCof : level.categoryWithCofibrations.cofibrations = I.rlp.llp)
    (data : FunctorialFactorizationData level.categoryWithCofibrations.cofibrations
      (level.categoryWithFibrations.fibrations ⊓
        level.categoryWithWeakEquivalences.weakEquivalences)) :
    FunctorialFactorizationData I.rlp.llp I.rlp :=
  data.ofLE hCof.le (level_trivialFibrations_eq level I hCof).le

/-- The full reclassified I middle functor is the original level record's value. -/
theorem originalIFromLevel_Z (level : ModelCategory C) (I : MorphismProperty C)
    (hCof : level.categoryWithCofibrations.cofibrations = I.rlp.llp)
    (data : FunctorialFactorizationData level.categoryWithCofibrations.cofibrations
      (level.categoryWithFibrations.fibrations ⊓
        level.categoryWithWeakEquivalences.weakEquivalences)) :
    (originalIFromLevel level I hCof data).Z = data.Z := rfl

/-- The full I inclusion family is the actual original level inclusion family. -/
theorem originalIFromLevel_i (level : ModelCategory C) (I : MorphismProperty C)
    (hCof : level.categoryWithCofibrations.cofibrations = I.rlp.llp)
    (data : FunctorialFactorizationData level.categoryWithCofibrations.cofibrations
      (level.categoryWithFibrations.fibrations ⊓
        level.categoryWithWeakEquivalences.weakEquivalences)) :
    (originalIFromLevel level I hCof data).i = data.i := rfl

/-- The full I projection family is the actual original level projection family. -/
theorem originalIFromLevel_p (level : ModelCategory C) (I : MorphismProperty C)
    (hCof : level.categoryWithCofibrations.cofibrations = I.rlp.llp)
    (data : FunctorialFactorizationData level.categoryWithCofibrations.cofibrations
      (level.categoryWithFibrations.fibrations ⊓
        level.categoryWithWeakEquivalences.weakEquivalences)) :
    (originalIFromLevel level I hCof data).p = data.p := rfl

section Assembly

variable [HasFiniteLimits C] [HasFiniteColimits C]
  (level : ModelCategory C) (I K W : MorphismProperty C)
  (hW : W.HasTwoOutOfThreeProperty) (hRight : I.rlp = K.rlp ⊓ W)
  (hAcyclic : K.rlp.llp ≤ W)
  (hCof : level.categoryWithCofibrations.cofibrations = I.rlp.llp)
  (givenLevelI : FunctorialFactorizationData level.categoryWithCofibrations.cofibrations
    (level.categoryWithFibrations.fibrations ⊓
      level.categoryWithWeakEquivalences.weakEquivalences))
  (givenK : FunctorialFactorizationData K.rlp.llp K.rlp)

/-- Construct the model using the original existing level I value and the given K value. -/
@[instance_reducible]
def modelCategoryFromLevel : ModelCategory C :=
  modelCategory I K W hW hRight hAcyclic
    (originalIFromLevel level I hCof givenLevelI) givenK

/-- The returned I data is the same original level record with only new membership proofs. -/
def cofibrantFactorizationFromLevel :
    letI : ModelCategory C :=
      modelCategoryFromLevel level I K W hW hRight hAcyclic hCof givenLevelI givenK
    FunctorialFactorizationData (cofibrations C) (trivialFibrations C) :=
  cofibrantFactorizationData I K W hW hRight hAcyclic
    (originalIFromLevel level I hCof givenLevelI) givenK

/-- The entire constructed I middle functor is the original level middle functor. -/
theorem cofibrantFactorizationFromLevel_Z :
    let : ModelCategory C :=
      modelCategoryFromLevel level I K W hW hRight hAcyclic hCof givenLevelI givenK
    (cofibrantFactorizationFromLevel level I K W hW hRight hAcyclic
      hCof givenLevelI givenK).Z = givenLevelI.Z := rfl

/-- The entire constructed I inclusion is the original level inclusion. -/
theorem cofibrantFactorizationFromLevel_i :
    let : ModelCategory C :=
      modelCategoryFromLevel level I K W hW hRight hAcyclic hCof givenLevelI givenK
    (cofibrantFactorizationFromLevel level I K W hW hRight hAcyclic
      hCof givenLevelI givenK).i = givenLevelI.i := rfl

/-- The entire constructed I projection is the original level projection. -/
theorem cofibrantFactorizationFromLevel_p :
    let : ModelCategory C :=
      modelCategoryFromLevel level I K W hW hRight hAcyclic hCof givenLevelI givenK
    (cofibrantFactorizationFromLevel level I K W hW hRight hAcyclic
      hCof givenLevelI givenK).p = givenLevelI.p := rfl

/-- Every original level I Arrow action remains the complete constructed I action. -/
theorem cofibrantFactorizationFromLevel_map {F G : Arrow C} (a : F ⟶ G) :
    let : ModelCategory C :=
      modelCategoryFromLevel level I K W hW hRight hAcyclic hCof givenLevelI givenK
    (cofibrantFactorizationFromLevel level I K W hW hRight hAcyclic
      hCof givenLevelI givenK).Z.map a = givenLevelI.Z.map a := rfl

/-- The whole constructed Q is the original level I value on the same initial arrows. -/
theorem cofibrantReplacementFromLevel_original (Z : C) (hZ : IsInitial Z) :
    cofibrantReplacement I K W hW hRight hAcyclic
        (originalIFromLevel level I hCof givenLevelI) givenK Z hZ =
      GivenFactorizationReplacements.initialArrows Z hZ ⋙ givenLevelI.Z := rfl

/-- The whole Q projection is the original level I projection function. -/
theorem cofibrantReplacementProjectionFromLevel_original (Z : C) (hZ : IsInitial Z)
    (X : C) :
    (cofibrantReplacementProjection I K W hW hRight hAcyclic
      (originalIFromLevel level I hCof givenLevelI) givenK Z hZ).app X =
        givenLevelI.p.app (Arrow.mk (hZ.to X)) := rfl

/-- The existing level dictionary and constructed dictionary form the genuine Quillen pair. -/
theorem fromLevel_isQuillen
    (hWeak : level.categoryWithWeakEquivalences.weakEquivalences ≤ W) :
    CategoryTheory.Adjunction.IsQuillenAdjunction
      (ExplicitModelIdentity.identityAdjunction level
        (modelCategoryFromLevel level I K W hW hRight hAcyclic hCof givenLevelI givenK)) :=
  ExplicitModelIdentity.identityAdjunction_isQuillen level
    (modelCategoryFromLevel level I K W hW hRight hAcyclic hCof givenLevelI givenK)
    hCof hWeak

end Assembly

end HomotopicalAlgebra.OriginalGeneratedModel
