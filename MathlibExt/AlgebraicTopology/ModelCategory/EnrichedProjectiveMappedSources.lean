/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjective
public import MathlibExt.CategoryTheory.SmallObject.MappedCellSourceSmallness

/-!
# Genuine projective models from the actual evaluated source-cell diagrams

The original base cardinal and caller bottom remain fixed. Both target
small-object arguments are derived from source Hom on the actual evaluated
free-cell chains. The coefficient tensor bounds derive the full evaluated
acyclicity, so the target model and all five classes are outputs.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w uA uV vV

open CategoryTheory Limits MorphismProperty Opposite MonoidalCategory

namespace HomotopicalAlgebra.EnrichedProjective.MappedSources

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [Small.{w} A] [LocallySmall.{w} V] [HasColimitsOfSize.{w, w} V]

/-- The original source-Hom premise on the actual evaluated free-cell diagrams at the given κ. -/
abbrev SourceCondition (P : MorphismProperty V) :=
  MappedCellSourceSmallness.Condition
    (fun a : A => EnrichedFunctorCat.Free.functor a)
    (fun a : A => EnrichedFunctorCat.evaluation a) P κ

/-- Every target eligibility field is derived from the same actual source-chain witnesses. -/
theorem generators_isCardinal (P : MorphismProperty V) [P.IsSmall.{w}]
    (hSource : SourceCondition (A := A) (κ := κ) P) :
    (generators (A := A) P).IsCardinalForSmallObjectArgument κ := by
  let _ : ∀ a : A, PreservesColimitsOfShape κ.ord.ToType
      (EnrichedFunctorCat.evaluation (V := V) a) := fun _ => inferInstance
  exact MappedCellSourceSmallness.isCardinalForSmallObjectArgument
    (fun a : A => EnrichedFunctorCat.Free.functor a)
    (fun a : A => EnrichedFunctorCat.evaluation a)
    P κ (fun a => EnrichedFunctorCat.Free.adjunction a) hSource

variable [ModelCategory V]
  (d : CofibrantGenerationData V κ)
  (hJ : ∀ a b : A, ∀ {X Y : V} (f : X ⟶ Y), d.J f → trivialCofibrations V (f ▷ (a ⟶[V] b)))
  (hSourceI : SourceCondition (A := A) (κ := κ) d.I)
  (hSourceJ : SourceCondition (A := A) (κ := κ) d.J)

include hJ hSourceI hSourceJ

/-- The genuine projective model is constructed from the original generation and mapped source-cell
data. -/
@[instance_reducible]
def modelCategory : ModelCategory (EnrichedFunctorCat V A) := by
  let L : A → V ⥤ EnrichedFunctorCat V A := fun a => EnrichedFunctorCat.Free.functor a
  let R : A → EnrichedFunctorCat V A ⥤ V := fun a => EnrichedFunctorCat.evaluation a
  let adj : ∀ a, L a ⊣ R a := fun a => EnrichedFunctorCat.Free.adjunction a
  let _ : HasFiniteLimits (EnrichedFunctorCat V A) := inferInstance
  let _ : HasFiniteColimits (EnrichedFunctorCat V A) := inferInstance
  let _ : ∀ a, PreservesColimitsOfSize.{w, w} (R a) := fun _ => inferInstance
  let _ : ∀ a, PreservesWellOrderContinuousOfShape κ.ord.ToType (R a) := fun _ =>
    { preservesColimitsOfShape := fun _ _ => inferInstance }
  let _ : d.I.IsSmall.{w} := d.I_smallObject.isSmall
  let _ : d.J.IsSmall.{w} := d.J_smallObject.isSmall
  let _ : (trivialCofibrations V).IsStableUnderCoproducts.{w} :=
    IsStableUnderCoproducts.of_llp_eq (trivialCofibrations V) (fibrations V) (fibrations_llp V)
  let _ : (trivialCofibrations V).IsStableUnderTransfiniteComposition.{w} := by
    rw [← fibrations_llp V]
    infer_instance
  let _ : (generators (A := A) d.I).IsCardinalForSmallObjectArgument κ := generators_isCardinal d.I
      hSourceI
  let _ : (generators (A := A) d.J).IsCardinalForSmallObjectArgument κ := generators_isCardinal d.J
      hSourceJ
  let _ : (generators (A := A) d.I).HasSmallObjectArgument.{w} :=
    ⟨κ, inferInstance, inferInstance, inferInstance⟩
  let _ : (generators (A := A) d.J).HasSmallObjectArgument.{w} :=
    ⟨κ, inferInstance, inferInstance, inferInstance⟩
  have hBase : d.I.rlp = d.J.rlp ⊓ weakEquivalences V := by
    rw [d.I_rlp, d.J_rlp]
    rfl
  have hEval : ∀ b, generators (A := A) d.J ≤ (trivialCofibrations V).inverseImage (R b) :=
    generators_evaluation_le d.J (trivialCofibrations V) hJ
  have hAcyclicity : (generators (A := A) d.J).rlp.llp ≤
      EvaluationTransfer.evaluationProperty R (weakEquivalences V) := by
    intro X Y f hf
    apply (EvaluationTransfer.evaluationProperty_iff R (weakEquivalences V) f).mpr
    intro a
    exact (rlp_llp_le_inverseImage_of_cardinal_closure
      (generators (A := A) d.J) (trivialCofibrations V) (R a) κ (hEval a) f hf).2
  exact EvaluationTransfer.evaluationProjectiveModelCategory.{w}
    L R adj d.I d.J (weakEquivalences V) hBase hAcyclicity

/-- The actual returned weak class consists of every original evaluated base weak equivalence. -/
theorem weakEquivalences_eq :
    letI : ModelCategory (EnrichedFunctorCat V A) := modelCategory d hJ hSourceI hSourceJ
    weakEquivalences (EnrichedFunctorCat V A) =
      EvaluationTransfer.evaluationProperty (fun a : A => EnrichedFunctorCat.evaluation a)
          (weakEquivalences V) := rfl

/-- The actual returned cofibration class is generated by the literal original free I images. -/
theorem cofibrations_eq :
    letI : ModelCategory (EnrichedFunctorCat V A) := modelCategory d hJ hSourceI hSourceJ
    cofibrations (EnrichedFunctorCat V A) = (generators (A := A) d.I).rlp.llp := rfl

/-- Every original evaluation detects the returned base fibration class. -/
theorem fibrations_eq :
    letI : ModelCategory (EnrichedFunctorCat V A) := modelCategory d hJ hSourceI hSourceJ
    fibrations (EnrichedFunctorCat V A) =
      EvaluationTransfer.evaluationProperty (fun a : A => EnrichedFunctorCat.evaluation a)
          (fibrations V) := by
  let _ : ModelCategory (EnrichedFunctorCat V A) := modelCategory d hJ hSourceI hSourceJ
  change (generators (A := A) d.J).rlp = _
  rw [EvaluationTransfer.evaluatedGenerators_rlp_eq
    (fun a : A => EnrichedFunctorCat.Free.functor a)
    (fun a : A => EnrichedFunctorCat.evaluation a)
    (fun a => EnrichedFunctorCat.Free.adjunction a) d.J, d.J_rlp]

/-- Every original evaluation detects the returned base trivial-fibration class. -/
theorem trivialFibrations_eq :
    letI : ModelCategory (EnrichedFunctorCat V A) := modelCategory d hJ hSourceI hSourceJ
    trivialFibrations (EnrichedFunctorCat V A) =
      EvaluationTransfer.evaluationProperty (fun a : A => EnrichedFunctorCat.evaluation a)
          (trivialFibrations V) := by
  let _ : ModelCategory (EnrichedFunctorCat V A) := modelCategory d hJ hSourceI hSourceJ
  change fibrations (EnrichedFunctorCat V A) ⊓ weakEquivalences (EnrichedFunctorCat V A) = _
  rw [fibrations_eq d hJ hSourceI hSourceJ, weakEquivalences_eq d hJ hSourceI hSourceJ]
  exact (EvaluationTransfer.evaluationProperty_inf _ (fibrations V) (weakEquivalences V)).symm

/-- The actual trivial-cofibration class is generated by the literal original free J images. -/
theorem trivialCofibrations_eq :
    letI : ModelCategory (EnrichedFunctorCat V A) := modelCategory d hJ hSourceI hSourceJ
    trivialCofibrations (EnrichedFunctorCat V A) = (generators (A := A) d.J).rlp.llp := by
  let _ : ModelCategory (EnrichedFunctorCat V A) := modelCategory d hJ hSourceI hSourceJ
  rw [← fibrations_llp (EnrichedFunctorCat V A)]
  rfl

/-- Every actual original free/evaluation adjunction is Quillen for the same constructed model. -/
theorem freeAtEvaluation_isQuillenAdjunction (a : A) :
    letI : ModelCategory (EnrichedFunctorCat V A) := modelCategory d hJ hSourceI hSourceJ
    (EnrichedFunctorCat.Free.adjunction (V := V) a).IsQuillenAdjunction := by
  let _ : ModelCategory (EnrichedFunctorCat V A) := modelCategory d hJ hSourceI hSourceJ
  apply Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations
  · intro X Y f hf
    rw [fibrations_eq d hJ hSourceI hSourceJ] at hf
    exact (EvaluationTransfer.evaluationProperty_iff _ (fibrations V) f).mp hf a
  · intro X Y f hf
    rw [trivialFibrations_eq d hJ hSourceI hSourceJ] at hf
    exact (EvaluationTransfer.evaluationProperty_iff _ (trivialFibrations V) f).mp hf a

end HomotopicalAlgebra.EnrichedProjective.MappedSources
