/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjective
public import MathlibExt.AlgebraicTopology.ModelCategory.MonoidAxiom

/-!
# Enriched projective models from the monoid axiom

Auxiliary cell classes control source smallness. The base monoid axiom
controls the actual evaluated J-cell complexes and their mapped retracts.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe w uA uV vV
open CategoryTheory Limits MonoidalCategory MorphismProperty Opposite

namespace HomotopicalAlgebra.EnrichedProjective

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V] [ModelCategory V]
  {A : Type uA} [EnrichedCategory V A]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]

/-- Literal evaluated free J-generators are tensors of base trivial cofibrations.
No isomorphism-invariance premise on the literal tensor family is needed. -/
theorem evaluation_generators_le_tensorTrivialCofibrations
    (d : CofibrantGenerationData V κ) (b : A) :
    generators (A := A) d.J ≤
      (tensorTrivialCofibrationsRight V).inverseImage (EnrichedFunctorCat.evaluation b) := by
  change MorphismProperty.ofHoms
    (fun q : A × d.J.toSet => (EnrichedFunctorCat.Free.functor q.1).map q.2.1.hom) ≤ _
  rw [MorphismProperty.ofHoms_le_iff]
  intro q
  have hBase := d.J.le_llp_rlp q.2.1.hom q.2.2
  rw [d.J_rlp, fibrations_llp] at hBase
  change tensorTrivialCofibrationsRight V
    (EnrichedFunctorCat.component
      ((EnrichedFunctorCat.Free.functor q.1).map q.2.1.hom) b)
  rw [EnrichedFunctorCat.Free.coefficientMap_component]
  exact whiskerRight_mem_tensorTrivialCofibrationsRight V q.2.1.hom hBase _

variable [HasColimitsOfSize.{w, w} V] [MonoidAxiom.{w} V]

/-- The base monoid axiom controls every actual evaluated cardinal J-cell endpoint. -/
theorem evaluated_J_left_le_weakEquivalences
    (d : CofibrantGenerationData V κ)
    [(generators (A := A) d.J).IsCardinalForSmallObjectArgument κ]
    (b : A) :
    (generators (A := A) d.J).rlp.llp ≤
      (weakEquivalences V).inverseImage (EnrichedFunctorCat.evaluation b) := by
  let _ : PreservesWellOrderContinuousOfShape κ.ord.ToType
      (EnrichedFunctorCat.evaluation (V := V) b) :=
    { preservesColimitsOfShape := fun _ _ => inferInstance }
  apply rlp_llp_le_inverseImage_of_cardinal_cells
    (generators (A := A) d.J) (weakEquivalences V)
    (EnrichedFunctorCat.evaluation b) κ
  intro X Y f c
  let mapped := c.mapOfLE (EnrichedFunctorCat.evaluation b)
    (generators (A := A) d.J) (tensorTrivialCofibrationsRight V)
    (evaluation_generators_le_tensorTrivialCofibrations d b)
  let transfinite := mapped.transfiniteCompositionOfShape'
    (I := tensorTrivialCofibrationsRight V) (fun s => s.i.2)
  apply MonoidAxiom.cellularClosure_le_weakEquivalences (C := V)
  rw [MorphismProperty.transfiniteCompositions_iff]
  exact ⟨κ.ord.ToType, inferInstance, inferInstance, inferInstance, inferInstance,
    transfinite.mem⟩

variable [Small.{w} A] [LocallySmall.{w} V]

variable (d : CofibrantGenerationData V κ)
  (QI QJ : MorphismProperty V)
  [QI.RespectsIso] [QJ.RespectsIso]
  [QI.IsStableUnderCoproducts.{w}] [QJ.IsStableUnderCoproducts.{w}]
  [QI.IsStableUnderCobaseChange] [QJ.IsStableUnderCobaseChange]
  [QI.IsStableUnderTransfiniteComposition.{w}]
  [QJ.IsStableUnderTransfiniteComposition.{w}]
  (hI : ∀ a b : A, ∀ {X Y : V} (f : X ⟶ Y),
    d.I f → QI (f ▷ (a ⟶[V] b)))
  (hJ : ∀ a b : A, ∀ {X Y : V} (f : X ⟶ Y),
    d.J f → QJ (f ▷ (a ⟶[V] b)))
  (hSourceI : ∀ {X Y : V} (f : X ⟶ Y), d.I f →
    ∀ (F : κ.ord.ToType ⥤ V) [F.IsWellOrderContinuous],
      (∀ ⦃a b⦄ (φ : a ⟶ b), QI (F.map φ)) →
      PreservesColimit F (coyoneda.obj (op X)))
  (hSourceJ : ∀ {X Y : V} (f : X ⟶ Y), d.J f →
    ∀ (F : κ.ord.ToType ⥤ V) [F.IsWellOrderContinuous],
      (∀ ⦃a b⦄ (φ : a ⟶ b), QJ (F.map φ)) →
      PreservesColimit F (coyoneda.obj (op X)))

/-- Construct the projective model from actual auxiliary source classes and the
base monoid axiom. Both target small-object arguments and evaluated acyclicity
are derived at the original cardinal. -/
@[instance_reducible]
def modelCategoryOfMonoidAxiom : ModelCategory (EnrichedFunctorCat V A) := by
  let L : A → V ⥤ EnrichedFunctorCat V A := fun a => EnrichedFunctorCat.Free.functor a
  let R : A → EnrichedFunctorCat V A ⥤ V := fun a => EnrichedFunctorCat.evaluation a
  let adj : ∀ a, L a ⊣ R a := fun a => EnrichedFunctorCat.Free.adjunction a
  let _ : HasFiniteLimits (EnrichedFunctorCat V A) := inferInstance
  let _ : HasFiniteColimits (EnrichedFunctorCat V A) := inferInstance
  let _ : HasIterationOfShape κ.ord.ToType (EnrichedFunctorCat V A) := inferInstance
  let _ : ∀ a, PreservesColimitsOfSize.{w, w} (R a) := fun a => inferInstance
  let _ : ∀ a, PreservesColimitsOfShape κ.ord.ToType (R a) := fun a => inferInstance
  let _ : ∀ a, PreservesWellOrderContinuousOfShape κ.ord.ToType (R a) := fun a =>
    { preservesColimitsOfShape := fun _ _ => inferInstance }
  let _ : d.I.IsSmall.{w} := d.I_smallObject.isSmall
  let _ : d.J.IsSmall.{w} := d.J_smallObject.isSmall
  let _ : (generators (A := A) d.I).IsCardinalForSmallObjectArgument κ :=
    generators_isCardinalForSmallObjectArgument d.I QI hI hSourceI
  let _ : (generators (A := A) d.J).IsCardinalForSmallObjectArgument κ :=
    generators_isCardinalForSmallObjectArgument d.J QJ hJ hSourceJ
  let _ : (generators (A := A) d.I).HasSmallObjectArgument.{w} :=
    ⟨⟨κ, inferInstance, inferInstance, inferInstance⟩⟩
  let _ : (generators (A := A) d.J).HasSmallObjectArgument.{w} :=
    ⟨⟨κ, inferInstance, inferInstance, inferInstance⟩⟩
  have hBase : d.I.rlp = d.J.rlp ⊓ weakEquivalences V := by
    rw [d.I_rlp, d.J_rlp]
    rfl
  have hAcyclicity : (generators (A := A) d.J).rlp.llp ≤
      EvaluationTransfer.evaluationProperty R (weakEquivalences V) := by
    intro X Y f hf
    apply (EvaluationTransfer.evaluationProperty_iff R (weakEquivalences V) f).2
    intro a
    exact evaluated_J_left_le_weakEquivalences d a f hf
  exact EvaluationTransfer.evaluationProjectiveModelCategory.{w}
    L R adj d.I d.J (weakEquivalences V) hBase hAcyclicity

include hI hJ hSourceI hSourceJ

/-- The constructed weak class is objectwise base weak equivalence. -/
theorem monoidAxiom_weakEquivalences_eq :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfMonoidAxiom d QI QJ hI hJ hSourceI hSourceJ
    weakEquivalences (EnrichedFunctorCat V A) =
      EvaluationTransfer.evaluationProperty
        (fun a : A => EnrichedFunctorCat.evaluation a) (weakEquivalences V) := by
  rfl

/-- Constructed cofibrations retain the literal free I-family. -/
theorem monoidAxiom_cofibrations_eq :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfMonoidAxiom d QI QJ hI hJ hSourceI hSourceJ
    cofibrations (EnrichedFunctorCat V A) = (generators (A := A) d.I).rlp.llp := by
  rfl

/-- Constructed fibrations are detected by each actual enriched evaluation. -/
theorem monoidAxiom_fibrations_eq :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfMonoidAxiom d QI QJ hI hJ hSourceI hSourceJ
    fibrations (EnrichedFunctorCat V A) =
      EvaluationTransfer.evaluationProperty
        (fun a : A => EnrichedFunctorCat.evaluation a) (fibrations V) := by
  let _ : ModelCategory (EnrichedFunctorCat V A) :=
    modelCategoryOfMonoidAxiom d QI QJ hI hJ hSourceI hSourceJ
  change (generators (A := A) d.J).rlp = _
  rw [EvaluationTransfer.evaluatedGenerators_rlp_eq
    (fun a : A => EnrichedFunctorCat.Free.functor a)
    (fun a : A => EnrichedFunctorCat.evaluation a)
    (fun a => EnrichedFunctorCat.Free.adjunction a) d.J, d.J_rlp]

/-- Constructed trivial fibrations retain the actual objectwise intersection. -/
theorem monoidAxiom_trivialFibrations_eq :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfMonoidAxiom d QI QJ hI hJ hSourceI hSourceJ
    trivialFibrations (EnrichedFunctorCat V A) =
      EvaluationTransfer.evaluationProperty
        (fun a : A => EnrichedFunctorCat.evaluation a) (trivialFibrations V) := by
  let _ : ModelCategory (EnrichedFunctorCat V A) :=
    modelCategoryOfMonoidAxiom d QI QJ hI hJ hSourceI hSourceJ
  change fibrations (EnrichedFunctorCat V A) ⊓ weakEquivalences (EnrichedFunctorCat V A) = _
  rw [monoidAxiom_fibrations_eq d QI QJ hI hJ hSourceI hSourceJ,
    monoidAxiom_weakEquivalences_eq d QI QJ hI hJ hSourceI hSourceJ]
  exact (EvaluationTransfer.evaluationProperty_inf _ (fibrations V)
    (weakEquivalences V)).symm

/-- Constructed trivial cofibrations retain the literal free J-left class. -/
theorem monoidAxiom_trivialCofibrations_eq :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfMonoidAxiom d QI QJ hI hJ hSourceI hSourceJ
    trivialCofibrations (EnrichedFunctorCat V A) = (generators (A := A) d.J).rlp.llp := by
  let _ : ModelCategory (EnrichedFunctorCat V A) :=
    modelCategoryOfMonoidAxiom d QI QJ hI hJ hSourceI hSourceJ
  rw [← fibrations_llp (EnrichedFunctorCat V A)]
  rfl

/-- Both actual functorial factorizations use the caller's original cardinal. -/
theorem monoidAxiom_functorialFactorizations :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfMonoidAxiom d QI QJ hI hJ hSourceI hSourceJ
    HasFunctorialFactorization (cofibrations (EnrichedFunctorCat V A))
        (trivialFibrations (EnrichedFunctorCat V A)) ∧
      HasFunctorialFactorization (trivialCofibrations (EnrichedFunctorCat V A))
        (fibrations (EnrichedFunctorCat V A)) := by
  let _ : ModelCategory (EnrichedFunctorCat V A) :=
    modelCategoryOfMonoidAxiom d QI QJ hI hJ hSourceI hSourceJ
  let _ : d.I.IsSmall.{w} := d.I_smallObject.isSmall
  let _ : d.J.IsSmall.{w} := d.J_smallObject.isSmall
  let _ : (generators (A := A) d.I).IsCardinalForSmallObjectArgument κ :=
    generators_isCardinalForSmallObjectArgument d.I QI hI hSourceI
  let _ : (generators (A := A) d.J).IsCardinalForSmallObjectArgument κ :=
    generators_isCardinalForSmallObjectArgument d.J QJ hJ hSourceJ
  constructor
  · rw [monoidAxiom_cofibrations_eq d QI QJ hI hJ hSourceI hSourceJ]
    have hRight : trivialFibrations (EnrichedFunctorCat V A) =
        (generators (A := A) d.I).rlp := by
      rw [monoidAxiom_trivialFibrations_eq d QI QJ hI hJ hSourceI hSourceJ,
        EvaluationTransfer.evaluatedGenerators_rlp_eq
          (fun a : A => EnrichedFunctorCat.Free.functor a)
          (fun a : A => EnrichedFunctorCat.evaluation a)
          (fun a => EnrichedFunctorCat.Free.adjunction a) d.I, d.I_rlp]
    rw [hRight]
    exact SmallObject.hasFunctorialFactorization (generators (A := A) d.I) κ
  · rw [monoidAxiom_trivialCofibrations_eq d QI QJ hI hJ hSourceI hSourceJ]
    change HasFunctorialFactorization (generators (A := A) d.J).rlp.llp
      (generators (A := A) d.J).rlp
    exact SmallObject.hasFunctorialFactorization (generators (A := A) d.J) κ

/-- The actual free/evaluation adjunction is Quillen for the selected model. -/
theorem monoidAxiom_freeAtEvaluation_isQuillenAdjunction (a : A) :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfMonoidAxiom d QI QJ hI hJ hSourceI hSourceJ
    (EnrichedFunctorCat.Free.adjunction (V := V) a).IsQuillenAdjunction := by
  let _ : ModelCategory (EnrichedFunctorCat V A) :=
    modelCategoryOfMonoidAxiom d QI QJ hI hJ hSourceI hSourceJ
  apply CategoryTheory.Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations
  · intro X Y f hf
    rw [monoidAxiom_fibrations_eq d QI QJ hI hJ hSourceI hSourceJ] at hf
    exact (EvaluationTransfer.evaluationProperty_iff _ (fibrations V) f).mp hf a
  · intro X Y f hf
    rw [monoidAxiom_trivialFibrations_eq d QI QJ hI hJ hSourceI hSourceJ] at hf
    exact (EvaluationTransfer.evaluationProperty_iff _ (trivialFibrations V) f).mp hf a

end HomotopicalAlgebra.EnrichedProjective
