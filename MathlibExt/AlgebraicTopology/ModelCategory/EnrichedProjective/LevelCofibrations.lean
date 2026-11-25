/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjective

/-!
# Complete evaluated left classes of enriched free generators

The literal base family and same-cardinal eligibility determine all evaluated
left arrows. Actual given-model generation data supply its class equations.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe w uA uV vV
open CategoryTheory Limits MorphismProperty MonoidalCategory
open HomotopicalAlgebra

namespace HomotopicalAlgebra.EnrichedProjective

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [HasColimitsOfSize.{w, w} V]

/-- All original free-generator left arrows evaluate into the proved base class. -/
theorem generatedLeft_le_evaluationProperty
    (P Q : MorphismProperty V)
    [(generators (A := A) P).IsCardinalForSmallObjectArgument κ]
    [Q.RespectsIso] [Q.IsStableUnderRetracts]
    [Q.IsStableUnderCoproducts.{w}] [Q.IsStableUnderCobaseChange]
    [Q.IsStableUnderTransfiniteCompositionOfShape κ.ord.ToType]
    (hTensor : ∀ a b : A, ∀ {X Y : V} (f : X ⟶ Y),
      P f → Q (f ▷ (a ⟶[V] b))) :
    (generators (A := A) P).rlp.llp ≤
      EvaluationTransfer.evaluationProperty (fun a : A => EnrichedFunctorCat.evaluation a) Q := by
  let (a : A) : PreservesWellOrderContinuousOfShape κ.ord.ToType
      (EnrichedFunctorCat.evaluation (V := V) a) :=
    { preservesColimitsOfShape := fun _ _ => inferInstance }
  intro X Y f hf
  apply (EvaluationTransfer.evaluationProperty_iff
    (fun a : A => EnrichedFunctorCat.evaluation a) Q f).2
  intro a
  exact (rlp_llp_le_inverseImage_of_cardinal_closure
    (generators (A := A) P) Q (EnrichedFunctorCat.evaluation a) κ
    (generators_evaluation_le P Q hTensor a)) f hf

section GivenModel

variable [ModelCategory (EnrichedFunctorCat V A)]

/-- Actual generation data identify and evaluate the whole given cofibration class. -/
theorem cofibrations_le_evaluationProperty
    (d : CofibrantGenerationData (EnrichedFunctorCat V A) κ)
    (P Q : MorphismProperty V) (hI : d.I = generators (A := A) P)
    [Q.RespectsIso] [Q.IsStableUnderRetracts]
    [Q.IsStableUnderCoproducts.{w}] [Q.IsStableUnderCobaseChange]
    [Q.IsStableUnderTransfiniteCompositionOfShape κ.ord.ToType]
    (hTensor : ∀ a b : A, ∀ {X Y : V} (f : X ⟶ Y),
      P f → Q (f ▷ (a ⟶[V] b))) :
    cofibrations (EnrichedFunctorCat V A) ≤
      EvaluationTransfer.evaluationProperty (fun a : A => EnrichedFunctorCat.evaluation a) Q := by
  have hEligible : (generators (A := A) P).IsCardinalForSmallObjectArgument κ := by
    rw [← hI]
    exact d.I_smallObject
  let _ := hEligible
  have hCof : cofibrations (EnrichedFunctorCat V A) =
      (generators (A := A) P).rlp.llp := by
    rw [← trivialFibrations_llp, ← d.I_rlp, hI]
  rw [hCof]
  exact generatedLeft_le_evaluationProperty (A := A) (κ := κ) P Q hTensor

/-- Actual generation data likewise evaluate the whole given trivial-cofibration class. -/
theorem trivialCofibrations_le_evaluationProperty
    (d : CofibrantGenerationData (EnrichedFunctorCat V A) κ)
    (P Q : MorphismProperty V) (hJ : d.J = generators (A := A) P)
    [Q.RespectsIso] [Q.IsStableUnderRetracts]
    [Q.IsStableUnderCoproducts.{w}] [Q.IsStableUnderCobaseChange]
    [Q.IsStableUnderTransfiniteCompositionOfShape κ.ord.ToType]
    (hTensor : ∀ a b : A, ∀ {X Y : V} (f : X ⟶ Y),
      P f → Q (f ▷ (a ⟶[V] b))) :
    trivialCofibrations (EnrichedFunctorCat V A) ≤
      EvaluationTransfer.evaluationProperty (fun a : A => EnrichedFunctorCat.evaluation a) Q := by
  have hEligible : (generators (A := A) P).IsCardinalForSmallObjectArgument κ := by
    rw [← hJ]
    exact d.J_smallObject
  let _ := hEligible
  have hCof : trivialCofibrations (EnrichedFunctorCat V A) =
      (generators (A := A) P).rlp.llp := by
    rw [← fibrations_llp, ← d.J_rlp, hJ]
  rw [hCof]
  exact generatedLeft_le_evaluationProperty (A := A) (κ := κ) P Q hTensor

end GivenModel
end HomotopicalAlgebra.EnrichedProjective
