/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module
public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveMonoidAxiom

set_option autoImplicit false
noncomputable section
universe w uA uV vV
open CategoryTheory Limits MonoidalCategory MorphismProperty Opposite HomotopicalAlgebra

namespace EnrichedProjectiveMonoidAxiomTests

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V] [ModelCategory V]
  {A : Type uA} [EnrichedCategory V A]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [Small.{w} A] [LocallySmall.{w} V] [HasColimitsOfSize.{w, w} V]
  [MonoidAxiom.{w} V]
  (d : CofibrantGenerationData V κ) (QI QJ : MorphismProperty V)
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

include hI hJ hSourceI hSourceJ

-- This context supplies only the base model and base source witnesses.
-- The target model, target small-object arguments and target acyclicity
-- are obtained from the actual constructor.
example : ModelCategory (EnrichedFunctorCat V A) :=
  EnrichedProjective.modelCategoryOfMonoidAxiom d QI QJ hI hJ hSourceI hSourceJ

section ChosenModel


example :
    let _ : ModelCategory (EnrichedFunctorCat V A) :=
      EnrichedProjective.modelCategoryOfMonoidAxiom d QI QJ hI hJ hSourceI hSourceJ
    weakEquivalences (EnrichedFunctorCat V A) =
    EvaluationTransfer.evaluationProperty
      (fun a : A => EnrichedFunctorCat.evaluation a) (weakEquivalences V) :=
  EnrichedProjective.monoidAxiom_weakEquivalences_eq d QI QJ hI hJ hSourceI hSourceJ

example :
    let _ : ModelCategory (EnrichedFunctorCat V A) :=
      EnrichedProjective.modelCategoryOfMonoidAxiom d QI QJ hI hJ hSourceI hSourceJ
    fibrations (EnrichedFunctorCat V A) =
    EvaluationTransfer.evaluationProperty
      (fun a : A => EnrichedFunctorCat.evaluation a) (fibrations V) :=
  EnrichedProjective.monoidAxiom_fibrations_eq d QI QJ hI hJ hSourceI hSourceJ

example :
    let _ : ModelCategory (EnrichedFunctorCat V A) :=
      EnrichedProjective.modelCategoryOfMonoidAxiom d QI QJ hI hJ hSourceI hSourceJ
    cofibrations (EnrichedFunctorCat V A) =
    (EnrichedProjective.generators (A := A) d.I).rlp.llp :=
  EnrichedProjective.monoidAxiom_cofibrations_eq d QI QJ hI hJ hSourceI hSourceJ

example :
    let _ : ModelCategory (EnrichedFunctorCat V A) :=
      EnrichedProjective.modelCategoryOfMonoidAxiom d QI QJ hI hJ hSourceI hSourceJ
    trivialFibrations (EnrichedFunctorCat V A) =
    EvaluationTransfer.evaluationProperty
      (fun a : A => EnrichedFunctorCat.evaluation a) (trivialFibrations V) :=
  EnrichedProjective.monoidAxiom_trivialFibrations_eq d QI QJ hI hJ hSourceI hSourceJ

example :
    let _ : ModelCategory (EnrichedFunctorCat V A) :=
      EnrichedProjective.modelCategoryOfMonoidAxiom d QI QJ hI hJ hSourceI hSourceJ
    trivialCofibrations (EnrichedFunctorCat V A) =
    (EnrichedProjective.generators (A := A) d.J).rlp.llp :=
  EnrichedProjective.monoidAxiom_trivialCofibrations_eq d QI QJ hI hJ hSourceI hSourceJ

example :
    let _ : ModelCategory (EnrichedFunctorCat V A) :=
      EnrichedProjective.modelCategoryOfMonoidAxiom d QI QJ hI hJ hSourceI hSourceJ
    HasFunctorialFactorization (cofibrations (EnrichedFunctorCat V A))
      (trivialFibrations (EnrichedFunctorCat V A)) ∧
    HasFunctorialFactorization (trivialCofibrations (EnrichedFunctorCat V A))
      (fibrations (EnrichedFunctorCat V A)) :=
  EnrichedProjective.monoidAxiom_functorialFactorizations d QI QJ hI hJ hSourceI hSourceJ

example (a : A) :
    let _ : ModelCategory (EnrichedFunctorCat V A) :=
      EnrichedProjective.modelCategoryOfMonoidAxiom d QI QJ hI hJ hSourceI hSourceJ
    (EnrichedFunctorCat.Free.adjunction (V := V) a).IsQuillenAdjunction :=
  EnrichedProjective.monoidAxiom_freeAtEvaluation_isQuillenAdjunction
    d QI QJ hI hJ hSourceI hSourceJ a

example (a : A) {X Y : V} (f : X ⟶ Y) (hf : d.I f) :
    let _ : ModelCategory (EnrichedFunctorCat V A) :=
      EnrichedProjective.modelCategoryOfMonoidAxiom d QI QJ hI hJ hSourceI hSourceJ

    cofibrations (EnrichedFunctorCat V A) ((EnrichedFunctorCat.Free.functor a).map f) := by
  let _ : ModelCategory (EnrichedFunctorCat V A) :=
    EnrichedProjective.modelCategoryOfMonoidAxiom d QI QJ hI hJ hSourceI hSourceJ
  dsimp only
  rw [EnrichedProjective.monoidAxiom_cofibrations_eq d QI QJ hI hJ hSourceI hSourceJ]
  exact (EnrichedProjective.generators (A := A) d.I).le_llp_rlp _
    (MorphismProperty.map_mem_adjointFamilyGenerators
      (fun b : A => EnrichedFunctorCat.Free.functor b) d.I a f hf)

example (a : A) {X Y : V} (f : X ⟶ Y) (hf : d.J f) :
    let _ : ModelCategory (EnrichedFunctorCat V A) :=
      EnrichedProjective.modelCategoryOfMonoidAxiom d QI QJ hI hJ hSourceI hSourceJ

    trivialCofibrations (EnrichedFunctorCat V A)
      ((EnrichedFunctorCat.Free.functor a).map f) := by
  let _ : ModelCategory (EnrichedFunctorCat V A) :=
    EnrichedProjective.modelCategoryOfMonoidAxiom d QI QJ hI hJ hSourceI hSourceJ
  dsimp only
  rw [EnrichedProjective.monoidAxiom_trivialCofibrations_eq d QI QJ hI hJ hSourceI hSourceJ]
  exact (EnrichedProjective.generators (A := A) d.J).le_llp_rlp _
    (MorphismProperty.map_mem_adjointFamilyGenerators
      (fun b : A => EnrichedFunctorCat.Free.functor b) d.J a f hf)

example :
    let _ : ModelCategory (EnrichedFunctorCat V A) :=
      EnrichedProjective.modelCategoryOfMonoidAxiom d QI QJ hI hJ hSourceI hSourceJ
    HasFiniteLimits (EnrichedFunctorCat V A) :=
  (EnrichedProjective.modelCategoryOfMonoidAxiom d QI QJ hI hJ hSourceI hSourceJ).cm1a
example :
    let _ : ModelCategory (EnrichedFunctorCat V A) :=
      EnrichedProjective.modelCategoryOfMonoidAxiom d QI QJ hI hJ hSourceI hSourceJ
    HasFiniteColimits (EnrichedFunctorCat V A) :=
  (EnrichedProjective.modelCategoryOfMonoidAxiom d QI QJ hI hJ hSourceI hSourceJ).cm1b

example {X Y : EnrichedFunctorCat V A} (f : X ⟶ Y) :
    let _ : ModelCategory (EnrichedFunctorCat V A) :=
      EnrichedProjective.modelCategoryOfMonoidAxiom d QI QJ hI hJ hSourceI hSourceJ

    ∃ (Z : EnrichedFunctorCat V A) (i : X ⟶ Z) (p : Z ⟶ Y),
      i ≫ p = f ∧ cofibrations (EnrichedFunctorCat V A) i ∧
        trivialFibrations (EnrichedFunctorCat V A) p := by
  let _ : ModelCategory (EnrichedFunctorCat V A) :=
    EnrichedProjective.modelCategoryOfMonoidAxiom d QI QJ hI hJ hSourceI hSourceJ
  let c := MorphismProperty.factorizationData
    (cofibrations (EnrichedFunctorCat V A)) (trivialFibrations (EnrichedFunctorCat V A)) f
  exact ⟨c.Z, c.i, c.p, c.fac, c.hi, c.hp⟩

example {X Y : EnrichedFunctorCat V A} (f : X ⟶ Y) :
    let _ : ModelCategory (EnrichedFunctorCat V A) :=
      EnrichedProjective.modelCategoryOfMonoidAxiom d QI QJ hI hJ hSourceI hSourceJ

    ∃ (Z : EnrichedFunctorCat V A) (i : X ⟶ Z) (p : Z ⟶ Y),
      i ≫ p = f ∧ trivialCofibrations (EnrichedFunctorCat V A) i ∧
        fibrations (EnrichedFunctorCat V A) p := by
  let _ : ModelCategory (EnrichedFunctorCat V A) :=
    EnrichedProjective.modelCategoryOfMonoidAxiom d QI QJ hI hJ hSourceI hSourceJ
  let c := MorphismProperty.factorizationData
    (trivialCofibrations (EnrichedFunctorCat V A)) (fibrations (EnrichedFunctorCat V A)) f
  exact ⟨c.Z, c.i, c.p, c.fac, c.hi, c.hp⟩

end ChosenModel
end EnrichedProjectiveMonoidAxiomTests
