/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.ZeroCompletion
public import MathlibExt.AlgebraicTopology.ModelCategory.EvaluationTransfer

/-!
# Evaluation classes under enriched zero completion

For a braided monoidal closed category with a zero object, restriction and extension along
the enriched zero completion preserve and reflect evaluationwise morphism properties that
contain identities and respect isomorphisms. The resulting equality identifies the completed
evaluation class with the inverse image of the original class under restriction.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uV vV uA
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalClosed ZeroObject

namespace CategoryTheory.EnrichedZeroCompletion

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V] [HasZeroObject V]
  {A : Type uA} [EnrichedCategory V A]

/-- Restriction preserves and reflects component properties invariant under isomorphism. -/
theorem restriction_evaluationProperty_iff (P : MorphismProperty V)
    [P.ContainsIdentities] [P.RespectsIso]
    {F G : EnrichedFunctorCat V (EnrichedZeroCompletion V A)} (t : F ⟶ G) :
    HomotopicalAlgebra.EvaluationTransfer.evaluationProperty
        (fun x : EnrichedZeroCompletion V A => EnrichedFunctorCat.evaluation x) P t ↔
      HomotopicalAlgebra.EvaluationTransfer.evaluationProperty
        (fun a : A => EnrichedFunctorCat.evaluation a) P (restriction.map t) := by
  rw [HomotopicalAlgebra.EvaluationTransfer.evaluationProperty_iff,
    HomotopicalAlgebra.EvaluationTransfer.evaluationProperty_iff]
  constructor
  · intro h a
    have ha := h (of a)
    change P (EnrichedFunctorCat.component t (of a)) at ha
    change P (EnrichedFunctorCat.component (restriction.map t) a)
    rw [restriction_map_component]
    exact ha
  · intro h x
    cases x with
    | none =>
      change P (EnrichedFunctorCat.component t zero)
      let _ := component_zero_isIso t
      exact P.of_isIso _
    | some a =>
      have ha := h a
      change P (EnrichedFunctorCat.component (restriction.map t) a) at ha
      change P (EnrichedFunctorCat.component t (of a))
      rw [restriction_map_component] at ha
      exact ha

/-- Extension preserves and reflects component properties invariant under isomorphism. -/
theorem extension_evaluationProperty_iff (P : MorphismProperty V)
    [P.ContainsIdentities] [P.RespectsIso]
    {F G : EnrichedFunctorCat V A} (t : F ⟶ G) :
    HomotopicalAlgebra.EvaluationTransfer.evaluationProperty
        (fun x : EnrichedZeroCompletion V A => EnrichedFunctorCat.evaluation x) P
          (extension.map t) ↔
      HomotopicalAlgebra.EvaluationTransfer.evaluationProperty
        (fun a : A => EnrichedFunctorCat.evaluation a) P t := by
  rw [HomotopicalAlgebra.EvaluationTransfer.evaluationProperty_iff,
    HomotopicalAlgebra.EvaluationTransfer.evaluationProperty_iff]
  constructor
  · intro h a
    have ha := h (of a)
    change P (EnrichedFunctorCat.component (extensionMap t) (of a)) at ha
    change P (EnrichedFunctorCat.component t a)
    rw [extensionMap_component_of] at ha
    exact ha
  · intro h x
    cases x with
    | none =>
      change P (EnrichedFunctorCat.component (extensionMap t) zero)
      let _ := component_zero_isIso (extensionMap t)
      exact P.of_isIso _
    | some a =>
      change P (EnrichedFunctorCat.component (extensionMap t) (of a))
      rw [extensionMap_component_of]
      exact h a

/-- Completed component properties are pulled back from original properties by restriction. -/
theorem evaluationProperty_completion_eq (P : MorphismProperty V)
    [P.ContainsIdentities] [P.RespectsIso] :
    HomotopicalAlgebra.EvaluationTransfer.evaluationProperty
        (fun x : EnrichedZeroCompletion V A => EnrichedFunctorCat.evaluation x) P =
      (HomotopicalAlgebra.EvaluationTransfer.evaluationProperty
        (fun a : A => EnrichedFunctorCat.evaluation a) P).inverseImage restriction := by
  ext F G t
  exact restriction_evaluationProperty_iff P t

end CategoryTheory.EnrichedZeroCompletion
