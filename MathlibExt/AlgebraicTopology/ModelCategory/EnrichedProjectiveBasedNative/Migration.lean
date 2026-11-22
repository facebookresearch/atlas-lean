/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveBasedNative.Classes
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedZeroCompletionEvaluation

/-!
# Complete native diagrams, literal strict diagrams and their actual classes

The actual completed-index unit law makes the added component a zero object.
This identifies the transported model on every completed component. The
literal full-subcategory inclusion preserves all five classes through the
actual restriction functor. Both carriers retain their distinct definitions.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory HomotopicalAlgebra MorphismProperty
open scoped MonoidalClosed ZeroObject CGWH.modelCategory

namespace HomotopicalAlgebra.EnrichedProjective.BasedNativePresentation

variable {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]

/-- The original non-base evaluation of the entire completed diagram. -/
def completedEvaluation (a : A) : CompletedCarrier (A := A) ⥤ PointedCGWH.{u, v} :=
  EnrichedFunctorCat.evaluation (EnrichedZeroCompletion.of a)

/-- The original free functor and actual full completed extension. -/
def completedFreeAt (a : A) : PointedCGWH.{u, v} ⥤ CompletedCarrier (A := A) :=
  NativePresentation.transportedFree completedEquivalence a

/-- Actual restriction retains the full original non-base object and every map. -/
def completedEvaluationIso (a : A) :
    completedEquivalence.functor ⋙ EnrichedFunctorCat.evaluation a ≅ completedEvaluation a :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro F G f
    change EnrichedFunctorCat.component (EnrichedZeroCompletion.restriction.map f) a ≫ 𝟙 _ =
      𝟙 _ ≫ EnrichedFunctorCat.component f (EnrichedZeroCompletion.of a)
    rw [EnrichedZeroCompletion.restriction_map_component]
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- The real native free adjunction through the actual complete extension/restriction. -/
def completedFreeAdjunction (a : A) : completedFreeAt a ⊣ completedEvaluation a :=
  NativePresentation.originalEvaluationAdjunction completedEquivalence a
    (completedEvaluation a) (completedEvaluationIso a)

/-- Whole completed-source free-I arrows retain their original non-base labels. -/
def completedBoundaryGenerators : MorphismProperty (CompletedCarrier (A := A)) :=
  MorphismProperty.adjointFamilyGenerators completedFreeAt
    PointedCGWH.realizedBoundaryInclusions.{u, v}

/-- Whole completed-source free-J arrows retain their original non-base labels. -/
def completedHornGenerators : MorphismProperty (CompletedCarrier (A := A)) :=
  MorphismProperty.adjointFamilyGenerators completedFreeAt
    PointedCGWH.realizedHornInclusions.{u, v}

variable [OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- The actual completed weak class is detected on every completed-index component. -/
theorem completed_weakEquivalences_iff {F G : CompletedCarrier (A := A)} (f : F ⟶ G) :
    let _ : ModelCategory (CompletedCarrier (A := A)) := completedModelCategory
    weakEquivalences (CompletedCarrier (A := A)) f ↔
      ∀ x : EnrichedZeroCompletion PointedCGWH.{u, v} A,
        weakEquivalences PointedCGWH.{u, v} (EnrichedFunctorCat.component f x) := by
  let _ : ModelCategory (CompletedCarrier (A := A)) := completedModelCategory
  change weakEquivalences (CompletedCarrier (A := A)) f ↔
    ∀ x, weakEquivalences PointedCGWH.{u, v} (EnrichedFunctorCat.component f x)
  rw [NativePresentation.weakEquivalences_eq completedEquivalence]
  exact (EnrichedZeroCompletion.restriction_evaluationProperty_iff _ f).symm.trans
    (EvaluationTransfer.evaluationProperty_iff _ _ f)

/-- The actual completed fibration class is detected on every completed-index component. -/
theorem completed_fibrations_iff {F G : CompletedCarrier (A := A)} (f : F ⟶ G) :
    let _ : ModelCategory (CompletedCarrier (A := A)) := completedModelCategory
    fibrations (CompletedCarrier (A := A)) f ↔
      ∀ x : EnrichedZeroCompletion PointedCGWH.{u, v} A,
        fibrations PointedCGWH.{u, v} (EnrichedFunctorCat.component f x) := by
  let _ : ModelCategory (CompletedCarrier (A := A)) := completedModelCategory
  change fibrations (CompletedCarrier (A := A)) f ↔
    ∀ x, fibrations PointedCGWH.{u, v} (EnrichedFunctorCat.component f x)
  rw [NativePresentation.fibrations_eq completedEquivalence]
  exact (EnrichedZeroCompletion.restriction_evaluationProperty_iff _ f).symm.trans
    (EvaluationTransfer.evaluationProperty_iff _ _ f)

/-- The actual complete intersection class includes the proved added-zero component. -/
theorem completed_trivialFibrations_iff {F G : CompletedCarrier (A := A)} (f : F ⟶ G) :
    let _ : ModelCategory (CompletedCarrier (A := A)) := completedModelCategory
    trivialFibrations (CompletedCarrier (A := A)) f ↔
      ∀ x : EnrichedZeroCompletion PointedCGWH.{u, v} A,
        trivialFibrations PointedCGWH.{u, v} (EnrichedFunctorCat.component f x) := by
  let _ : ModelCategory (CompletedCarrier (A := A)) := completedModelCategory
  change trivialFibrations (CompletedCarrier (A := A)) f ↔
    ∀ x, trivialFibrations PointedCGWH.{u, v} (EnrichedFunctorCat.component f x)
  rw [NativePresentation.trivialFibrations_eq completedEquivalence]
  exact (EnrichedZeroCompletion.restriction_evaluationProperty_iff _ f).symm.trans
    (EvaluationTransfer.evaluationProperty_iff _ _ f)

/-- Actual completed cofibrations are the full original non-base free-I left class. -/
theorem completed_cofibrations_eq :
    let _ : ModelCategory (CompletedCarrier (A := A)) := completedModelCategory
    cofibrations (CompletedCarrier (A := A)) = completedBoundaryGenerators.rlp.llp :=
  NativePresentation.cofibrations_eq_originalGenerators completedEquivalence
    id Function.surjective_id completedFreeAt completedEvaluation completedFreeAdjunction
      completedEvaluationIso

/-- Actual completed trivial cofibrations are the full original non-base free-J left class. -/
theorem completed_trivialCofibrations_eq :
    let _ : ModelCategory (CompletedCarrier (A := A)) := completedModelCategory
    trivialCofibrations (CompletedCarrier (A := A)) = completedHornGenerators.rlp.llp :=
  NativePresentation.trivialCofibrations_eq_originalGenerators completedEquivalence
    id Function.surjective_id completedFreeAt completedEvaluation completedFreeAdjunction
      completedEvaluationIso

/-- The full original completed free/evaluation adjunction is actually Quillen. -/
theorem completedFreeAdjunction_isQuillen (a : A) :
    let _ : ModelCategory (CompletedCarrier (A := A)) := completedModelCategory
    (completedFreeAdjunction a).IsQuillenAdjunction :=
  NativePresentation.originalFreeEvaluation_isQuillenAdjunction completedEquivalence
    a (completedFreeAt a) (completedEvaluation a) (completedFreeAdjunction a)
      (completedEvaluationIso a)

/-- The literal strict inclusion preserves the same actual whole weak class. -/
theorem strict_inclusion_weakEquivalences_iff {F G : StrictCarrier (A := A)} (f : F ⟶ G) :
    (let _ : ModelCategory (CompletedCarrier (A := A)) := completedModelCategory
     weakEquivalences (CompletedCarrier (A := A))
       ((EnrichedZeroCompletion.basePreserving.ι).map f)) ↔
    (let _ : ModelCategory (StrictCarrier (A := A)) := strictModelCategory
     weakEquivalences (StrictCarrier (A := A)) f) := by rfl

/-- The literal strict inclusion preserves the same actual whole fibration class. -/
theorem strict_inclusion_fibrations_iff {F G : StrictCarrier (A := A)} (f : F ⟶ G) :
    (let _ : ModelCategory (CompletedCarrier (A := A)) := completedModelCategory
     fibrations (CompletedCarrier (A := A))
       ((EnrichedZeroCompletion.basePreserving.ι).map f)) ↔
    (let _ : ModelCategory (StrictCarrier (A := A)) := strictModelCategory
     fibrations (StrictCarrier (A := A)) f) := by rfl

/-- The literal strict inclusion preserves the same actual whole trivial-fibration class. -/
theorem strict_inclusion_trivialFibrations_iff {F G : StrictCarrier (A := A)} (f : F ⟶ G) :
    (let _ : ModelCategory (CompletedCarrier (A := A)) := completedModelCategory
     trivialFibrations (CompletedCarrier (A := A))
       ((EnrichedZeroCompletion.basePreserving.ι).map f)) ↔
    (let _ : ModelCategory (StrictCarrier (A := A)) := strictModelCategory
     trivialFibrations (StrictCarrier (A := A)) f) := by rfl

/-- The literal strict inclusion preserves the same actual whole cofibration class. -/
theorem strict_inclusion_cofibrations_iff {F G : StrictCarrier (A := A)} (f : F ⟶ G) :
    (let _ : ModelCategory (CompletedCarrier (A := A)) := completedModelCategory
     cofibrations (CompletedCarrier (A := A))
       ((EnrichedZeroCompletion.basePreserving.ι).map f)) ↔
    (let _ : ModelCategory (StrictCarrier (A := A)) := strictModelCategory
     cofibrations (StrictCarrier (A := A)) f) := by rfl

/-- The literal strict inclusion preserves the same actual whole trivial-cofibration class. -/
theorem strict_inclusion_trivialCofibrations_iff {F G : StrictCarrier (A := A)} (f : F ⟶ G) :
    (let _ : ModelCategory (CompletedCarrier (A := A)) := completedModelCategory
     trivialCofibrations (CompletedCarrier (A := A))
       ((EnrichedZeroCompletion.basePreserving.ι).map f)) ↔
    (let _ : ModelCategory (StrictCarrier (A := A)) := strictModelCategory
     trivialCofibrations (StrictCarrier (A := A)) f) := by rfl

end HomotopicalAlgebra.EnrichedProjective.BasedNativePresentation
