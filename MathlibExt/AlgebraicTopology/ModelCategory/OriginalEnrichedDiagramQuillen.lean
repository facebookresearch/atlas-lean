/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.OriginalEnrichedProjective
public import MathlibExt.CategoryTheory.Enriched.LeftKanExtension
public import MathlibExt.CategoryTheory.Enriched.RightKanExtension
public import Mathlib.CategoryTheory.LiftingProperties.Adjunction

/-!
# Quillen criteria for the same original enriched projective models

Evaluation and restriction retain their original genuine components. The
particular enriched left Kan / restriction and restriction / right Kan
adjunctions are used directly. The right-Kan criterion tests only the
literal original generating arrows, rather than assuming final Quillen
preservation or either diagram model dictionary.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
noncomputable section

universe w uA uB uV vV

open CategoryTheory Limits MorphismProperty MonoidalCategory

namespace HomotopicalAlgebra.OriginalEnrichedDiagramQuillen

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V] [ModelCategory V]
  {A : Type uA} [EnrichedCategory V A]
  {B : Type uB} [EnrichedCategory V B]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [Small.{w} A] [Small.{w} B] [LocallySmall.{w} V] [HasColimitsOfSize.{w, w} V]
  (d : CofibrantGenerationData V κ)
  (sA : OriginalEnrichedProjective.SourceConditions (A := A) d)
  (sB : OriginalEnrichedProjective.SourceConditions (A := B) d)

/-- Every evaluation preserves the original constructed projective left classes as well. -/
theorem evaluation_left_classes (a : A) :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      EnrichedProjective.modelCategory d sA.I_tensor sA.J_tensor sA.I_source sA.J_source
    PreservesCofibrations (EnrichedFunctorCat.evaluation (V := V) a) ∧
      PreservesTrivialCofibrations (EnrichedFunctorCat.evaluation (V := V) a) := by
  let _ : ModelCategory (EnrichedFunctorCat V A) :=
    EnrichedProjective.modelCategory d sA.I_tensor sA.J_tensor sA.I_source sA.J_source
  let _ : (cofibrations V).IsStableUnderCoproducts.{w} :=
    IsStableUnderCoproducts.of_llp_eq (cofibrations V) (trivialFibrations V)
      (trivialFibrations_llp V)
  let _ : (trivialCofibrations V).IsStableUnderCoproducts.{w} :=
    IsStableUnderCoproducts.of_llp_eq (trivialCofibrations V) (fibrations V) (fibrations_llp V)
  let _ : (cofibrations V).IsStableUnderTransfiniteComposition.{w} := by
    rw [← trivialFibrations_llp V]
    infer_instance
  let _ : (trivialCofibrations V).IsStableUnderTransfiniteComposition.{w} := by
    rw [← fibrations_llp V]
    infer_instance
  let E := OriginalEnrichedProjective.generationData d sA
  have hC := EnrichedProjective.cofibrations_le_evaluationProperty E d.I
    (cofibrations V) rfl sA.I_tensor
  have hT := EnrichedProjective.trivialCofibrations_le_evaluationProperty E d.J
    (trivialCofibrations V) rfl sA.J_tensor
  constructor
  · intro F G f hf
    exact (EvaluationTransfer.evaluationProperty_iff
      (fun b : A => EnrichedFunctorCat.evaluation (V := V) b) (cofibrations V) f).mp (hC f hf) a
  · intro F G f hf
    exact (EvaluationTransfer.evaluationProperty_iff
      (fun b : A => EnrichedFunctorCat.evaluation (V := V) b)
        (trivialCofibrations V) f).mp (hT f hf) a

/-- Any actual evaluation/right-adjoint pair is Quillen on this same constructed model. -/
theorem evaluation_left_isQuillen (a : A) (R : V ⥤ EnrichedFunctorCat V A)
    (adj : EnrichedFunctorCat.evaluation a ⊣ R) :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      EnrichedProjective.modelCategory d sA.I_tensor sA.J_tensor sA.I_source sA.J_source
    adj.IsQuillenAdjunction := by
  let _ : ModelCategory (EnrichedFunctorCat V A) :=
    EnrichedProjective.modelCategory d sA.I_tensor sA.J_tensor sA.I_source sA.J_source
  have h := evaluation_left_classes d sA a
  exact ⟨h.1, h.2⟩

/-- Every original restriction component preserves the constructed projective right classes. -/
theorem restriction_right_classes (u : EnrichedFunctor V A B) :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      EnrichedProjective.modelCategory d sA.I_tensor sA.J_tensor sA.I_source sA.J_source
    letI : ModelCategory (EnrichedFunctorCat V B) :=
      EnrichedProjective.modelCategory d sB.I_tensor sB.J_tensor sB.I_source sB.J_source
    PreservesFibrations (EnrichedFunctorCat.restriction u) ∧
      PreservesTrivialFibrations (EnrichedFunctorCat.restriction u) := by
  let _ : ModelCategory (EnrichedFunctorCat V A) :=
    EnrichedProjective.modelCategory d sA.I_tensor sA.J_tensor sA.I_source sA.J_source
  let _ : ModelCategory (EnrichedFunctorCat V B) :=
    EnrichedProjective.modelCategory d sB.I_tensor sB.J_tensor sB.I_source sB.J_source
  constructor
  · intro X Y f hf
    rw [EnrichedProjective.fibrations_eq d sB.I_tensor sB.J_tensor sB.I_source sB.J_source] at hf
    rw [EnrichedProjective.fibrations_eq d sA.I_tensor sA.J_tensor sA.I_source sA.J_source]
    change EvaluationTransfer.evaluationProperty
      (fun a : A => EnrichedFunctorCat.evaluation a) (fibrations V)
        ((EnrichedFunctorCat.restriction u).map f)
    apply (EvaluationTransfer.evaluationProperty_iff
      (fun a : A => EnrichedFunctorCat.evaluation (V := V) a) (fibrations V)
        ((EnrichedFunctorCat.restriction u).map f)).mpr
    intro a
    change fibrations V (EnrichedFunctorCat.component (EnrichedFunctorCat.restrictionMap u f) a)
    rw [EnrichedFunctorCat.restrictionMap_component]
    exact (EvaluationTransfer.evaluationProperty_iff
      (fun b : B => EnrichedFunctorCat.evaluation (V := V) b) (fibrations V) f).mp hf (u.obj a)
  · intro X Y f hf
    rw [EnrichedProjective.trivialFibrations_eq d
      sB.I_tensor sB.J_tensor sB.I_source sB.J_source] at hf
    rw [EnrichedProjective.trivialFibrations_eq d
      sA.I_tensor sA.J_tensor sA.I_source sA.J_source]
    change EvaluationTransfer.evaluationProperty
      (fun a : A => EnrichedFunctorCat.evaluation a) (trivialFibrations V)
        ((EnrichedFunctorCat.restriction u).map f)
    apply (EvaluationTransfer.evaluationProperty_iff
      (fun a : A => EnrichedFunctorCat.evaluation (V := V) a) (trivialFibrations V)
        ((EnrichedFunctorCat.restriction u).map f)).mpr
    intro a
    change trivialFibrations V
      (EnrichedFunctorCat.component (EnrichedFunctorCat.restrictionMap u f) a)
    rw [EnrichedFunctorCat.restrictionMap_component]
    exact (EvaluationTransfer.evaluationProperty_iff
      (fun b : B => EnrichedFunctorCat.evaluation (V := V) b) (trivialFibrations V) f).mp hf
          (u.obj a)

/-- The actual original enriched left Kan adjunction is Quillen on the constructed models. -/
theorem leftKan_isQuillen (u : EnrichedFunctor V A B)
    [HasCoproducts.{uA} V] [HasCoequalizers V] :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      EnrichedProjective.modelCategory d sA.I_tensor sA.J_tensor sA.I_source sA.J_source
    letI : ModelCategory (EnrichedFunctorCat V B) :=
      EnrichedProjective.modelCategory d sB.I_tensor sB.J_tensor sB.I_source sB.J_source
    (EnrichedFunctorCat.leftKanRestrictionAdjunction u).IsQuillenAdjunction := by
  let _ : ModelCategory (EnrichedFunctorCat V A) :=
    EnrichedProjective.modelCategory d sA.I_tensor sA.J_tensor sA.I_source sA.J_source
  let _ : ModelCategory (EnrichedFunctorCat V B) :=
    EnrichedProjective.modelCategory d sB.I_tensor sB.J_tensor sB.I_source sB.J_source
  have h := restriction_right_classes d sA sB u
  exact Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations h.1 h.2

private theorem mapped_left_class
    {C D : Type*} [Category* C] [Category* D]
    (P : MorphismProperty C) (Q : MorphismProperty D)
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (h : P ≤ Q.rlp.llp.inverseImage L) :
    P.rlp.llp ≤ Q.rlp.llp.inverseImage L := by
  intro X Y f hf X' Y' p hp
  apply (adj.hasLiftingProperty_iff f p).mpr
  apply hf
  intro Z W i hi
  exact (adj.hasLiftingProperty_iff i p).mp (h i hi p hp)

/-- Genuine original generator restrictions construct the left-class preservation needed for Ran. -/
theorem restriction_left_classes_of_generators (u : EnrichedFunctor V A B)
    [HasProducts.{uA} V] [HasEqualizers V]
    (hI : EnrichedProjective.generators (A := B) d.I ≤
      (EnrichedProjective.generators (A := A) d.I).rlp.llp.inverseImage
        (EnrichedFunctorCat.restriction u))
    (hJ : EnrichedProjective.generators (A := B) d.J ≤
      (EnrichedProjective.generators (A := A) d.J).rlp.llp.inverseImage
        (EnrichedFunctorCat.restriction u)) :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      EnrichedProjective.modelCategory d sA.I_tensor sA.J_tensor sA.I_source sA.J_source
    letI : ModelCategory (EnrichedFunctorCat V B) :=
      EnrichedProjective.modelCategory d sB.I_tensor sB.J_tensor sB.I_source sB.J_source
    PreservesCofibrations (EnrichedFunctorCat.restriction u) ∧
      PreservesTrivialCofibrations (EnrichedFunctorCat.restriction u) := by
  let _ : ModelCategory (EnrichedFunctorCat V A) :=
    EnrichedProjective.modelCategory d sA.I_tensor sA.J_tensor sA.I_source sA.J_source
  let _ : ModelCategory (EnrichedFunctorCat V B) :=
    EnrichedProjective.modelCategory d sB.I_tensor sB.J_tensor sB.I_source sB.J_source
  constructor
  · change cofibrations (EnrichedFunctorCat V B) ≤
      (cofibrations (EnrichedFunctorCat V A)).inverseImage (EnrichedFunctorCat.restriction u)
    rw [EnrichedProjective.cofibrations_eq d sA.I_tensor sA.J_tensor sA.I_source sA.J_source,
      EnrichedProjective.cofibrations_eq d sB.I_tensor sB.J_tensor sB.I_source sB.J_source]
    exact mapped_left_class _ _ (EnrichedFunctorCat.rightKanAdjunction u) hI
  · change trivialCofibrations (EnrichedFunctorCat V B) ≤
      (trivialCofibrations (EnrichedFunctorCat V A)).inverseImage (EnrichedFunctorCat.restriction u)
    rw [EnrichedProjective.trivialCofibrations_eq d
      sA.I_tensor sA.J_tensor sA.I_source sA.J_source,
      EnrichedProjective.trivialCofibrations_eq d
      sB.I_tensor sB.J_tensor sB.I_source sB.J_source]
    exact mapped_left_class _ _ (EnrichedFunctorCat.rightKanAdjunction u) hJ

/-- The particular genuine Ran adjunction is Quillen from the original generator criteria. -/
theorem rightKan_isQuillen_of_generators (u : EnrichedFunctor V A B)
    [HasProducts.{uA} V] [HasEqualizers V]
    (hI : EnrichedProjective.generators (A := B) d.I ≤
      (EnrichedProjective.generators (A := A) d.I).rlp.llp.inverseImage
        (EnrichedFunctorCat.restriction u))
    (hJ : EnrichedProjective.generators (A := B) d.J ≤
      (EnrichedProjective.generators (A := A) d.J).rlp.llp.inverseImage
        (EnrichedFunctorCat.restriction u)) :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      EnrichedProjective.modelCategory d sA.I_tensor sA.J_tensor sA.I_source sA.J_source
    letI : ModelCategory (EnrichedFunctorCat V B) :=
      EnrichedProjective.modelCategory d sB.I_tensor sB.J_tensor sB.I_source sB.J_source
    (EnrichedFunctorCat.rightKanAdjunction u).IsQuillenAdjunction := by
  let _ : ModelCategory (EnrichedFunctorCat V A) :=
    EnrichedProjective.modelCategory d sA.I_tensor sA.J_tensor sA.I_source sA.J_source
  let _ : ModelCategory (EnrichedFunctorCat V B) :=
    EnrichedProjective.modelCategory d sB.I_tensor sB.J_tensor sB.I_source sB.J_source
  have h := restriction_left_classes_of_generators d sA sB u hI hJ
  exact ⟨h.1, h.2⟩

end HomotopicalAlgebra.OriginalEnrichedDiagramQuillen
