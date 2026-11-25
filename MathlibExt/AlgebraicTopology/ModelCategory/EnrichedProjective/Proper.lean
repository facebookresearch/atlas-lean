/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjective.LevelCofibrations
public import MathlibExt.AlgebraicTopology.ModelCategory.EvaluationTransfer.Proper
public import MathlibExt.AlgebraicTopology.ModelCategory.MonoidalQuillen

/-!
# Properness of the same given enriched projective model

The original generation record gives the whole cofibration class. Actual
Hom-tensor closure and evaluated weak detection prove arbitrary-source
properness. The model, cardinal, families and factor choices remain fixed.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe w uA uV vV
open CategoryTheory Limits MorphismProperty MonoidalCategory
open HomotopicalAlgebra

namespace HomotopicalAlgebra.EnrichedProjective

section TensorPredicate

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V] [ModelCategory V]
  {A : Type uA} [EnrichedCategory V A]
  [ModelCategory (EnrichedFunctorCat V A)]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [HasColimitsOfSize.{w, w} V]

/-- Actual I generation and tensor membership prove properness of the given model. -/
theorem isLeftProper_of_generatorTensor
    (d : CofibrantGenerationData (EnrichedFunctorCat V A) κ)
    (P Q : MorphismProperty V) (hI : d.I = generators (A := A) P)
    [Q.RespectsIso] [Q.IsStableUnderRetracts]
    [Q.IsStableUnderCoproducts.{w}] [Q.IsStableUnderCobaseChange]
    [Q.IsStableUnderTransfiniteCompositionOfShape κ.ord.ToType]
    (hW : weakEquivalences (EnrichedFunctorCat V A) =
      EvaluationTransfer.evaluationProperty
        (fun a : A => EnrichedFunctorCat.evaluation a) (weakEquivalences V))
    (hTensor : ∀ a b : A, ∀ {X Y : V} (f : X ⟶ Y),
      P f → Q (f ▷ (a ⟶[V] b)))
    (hBase : (weakEquivalences V).IsStableUnderCobaseChangeAgainst Q) :
    IsLeftProper (EnrichedFunctorCat V A) :=
  EvaluationTransfer.isLeftProper_of_evaluations
    (fun a : A => EnrichedFunctorCat.evaluation a) Q hW
    (cofibrations_le_evaluationProperty d P Q hI hTensor) hBase
    (by intro a X Y Z i f hi hf; infer_instance)

end TensorPredicate

section CofibrantHoms

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V] [ModelCategory V]
  [IsClosedSymmetricMonoidalModelCategory V] [IsLeftProper V]
  {A : Type uA} [EnrichedCategory V A]
  [ModelCategory (EnrichedFunctorCat V A)]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [HasColimitsOfSize.{w, w} V]

/-- Actual cofibrant Hom objects derive tensor membership through the original braiding. -/
theorem isLeftProper_of_isCofibrant_homs
    (d : CofibrantGenerationData (EnrichedFunctorCat V A) κ)
    (P : MorphismProperty V) (hI : d.I = generators (A := A) P)
    (hP : P ≤ cofibrations V)
    (hW : weakEquivalences (EnrichedFunctorCat V A) =
      EvaluationTransfer.evaluationProperty
        (fun a : A => EnrichedFunctorCat.evaluation a) (weakEquivalences V))
    (hHom : ∀ a b : A, IsCofibrant (a ⟶[V] b)) :
    IsLeftProper (EnrichedFunctorCat V A) := by
  let _ : (cofibrations V).IsStableUnderCoproducts.{w} :=
    IsStableUnderCoproducts.of_llp_eq (cofibrations V)
      (trivialFibrations V) (trivialFibrations_llp V)
  let _ : (cofibrations V).IsStableUnderTransfiniteCompositionOfShape κ.ord.ToType := by
    rw [← trivialFibrations_llp]
    infer_instance
  have hTensor (a b : A) {X Y : V} (f : X ⟶ Y) (hf : P f) :
      cofibrations V (f ▷ (a ⟶[V] b)) := by
    let _ : IsCofibrant (a ⟶[V] b) := hHom a b
    have hleft : cofibrations V ((a ⟶[V] b) ◁ f) :=
      (ihomAdjunction_isQuillenAdjunction_of_isCofibrant
        (a ⟶[V] b)).preservesCofibrations f (hP f hf)
    let e : Arrow.mk ((a ⟶[V] b) ◁ f) ≅ Arrow.mk (f ▷ (a ⟶[V] b)) :=
      Arrow.isoMk (β_ (a ⟶[V] b) X) (β_ (a ⟶[V] b) Y)
        (BraidedCategory.braiding_naturality_right (a ⟶[V] b) f).symm
    exact ((cofibrations V).arrow_mk_iso_iff e).mp hleft
  exact isLeftProper_of_generatorTensor d P (cofibrations V) hI hW hTensor inferInstance

end CofibrantHoms
end HomotopicalAlgebra.EnrichedProjective
