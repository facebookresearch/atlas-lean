/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.GenericSourcePowers

/-!
# Complete function-square predicates at the selected source context

The source monoidal and closed structures are bound before the whole function
and drop families. The forward and inverse formulas retain every source unit
arrow, degree and target object.
-/

set_option autoImplicit false

section FullLiteralSourceFunctionPredicates
noncomputable section
universe uLiteralV vLiteralV uLiteralJ
open CategoryTheory MonoidalCategory Limits
open CategoryTheory.EnrichedFunctorCat
open PointedCGWH.Spectra.Orthogonal
open scoped MonoidalClosed
attribute [local instance] Enriched.prodCategory MonoidalLeftAction.monoidalOppositeLeftAction

namespace PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.TypedFullPowerData

variable {V : Type uLiteralV} [Category.{vLiteralV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  [Category ℕ] [MonoidalCategory ℕ] [SymmetricCategory ℕ]
  [EnrichedOrdinaryCategory V ℕ] [HasColimitsOfSize.{0, 0} V]
  [HasProducts.{0} V] [HasEqualizers V]
  {q : Enriched.ModuleMappingR.SelectedSource V ℕ}
  {J : Type uLiteralJ} [EnrichedCategory V J]
  (c : CanonicalSourceFreeSmash.SelectedPair.Context q J)

/-- The literal forward predicate selects the complete source and closed dictionaries
before the entire function and drop families are typed. -/
def LiteralFunctionDropFormula
    (source : CanonicalSourceSmash.SourceContext q (EnrichedFunctorCat V J))
    (P : ℕ → EnrichedFunctorCat V J) :
    letI := source.monoidalCategory
    letI := CanonicalSourceSmashClosed.Selected.monoidalClosed source
    (∀ n : ℕ, ihom (P n) ≅ Functor.Iteration.iterate (ihom (P 1)) n) →
      ((P 1 ⟶ 𝟙_ (EnrichedFunctorCat V J)) → ∀ n : ℕ, P (n + 1) ⟶ P n) → Prop :=
  letI := source.monoidalCategory
  letI := CanonicalSourceSmashClosed.Selected.monoidalClosed source
  fun F d => ∀ (l : P 1 ⟶ 𝟙_ (EnrichedFunctorCat V J)) (n : ℕ) (X : EnrichedFunctorCat V J),
    (MonoidalClosed.pre (d l n)).app X ≫ (F (n + 1)).hom.app X =
      (F n).hom.app X ≫ (Functor.Iteration.inputTransition (Powers.sourceUnitCoaugmentation l) n).app X

/-- The literal inverse predicate retains the same whole source, function and drop
families and every original unit arrow, degree and target. -/
def LiteralFunctionDropInverseFormula
    (source : CanonicalSourceSmash.SourceContext q (EnrichedFunctorCat V J))
    (P : ℕ → EnrichedFunctorCat V J) :
    letI := source.monoidalCategory
    letI := CanonicalSourceSmashClosed.Selected.monoidalClosed source
    (∀ n : ℕ, ihom (P n) ≅ Functor.Iteration.iterate (ihom (P 1)) n) →
      ((P 1 ⟶ 𝟙_ (EnrichedFunctorCat V J)) → ∀ n : ℕ, P (n + 1) ⟶ P n) → Prop :=
  letI := source.monoidalCategory
  letI := CanonicalSourceSmashClosed.Selected.monoidalClosed source
  fun F d => ∀ (l : P 1 ⟶ 𝟙_ (EnrichedFunctorCat V J)) (n : ℕ) (X : EnrichedFunctorCat V J),
    (Functor.Iteration.inputTransition (Powers.sourceUnitCoaugmentation l) n).app X ≫
        (F (n + 1)).inv.app X =
      (F n).inv.app X ≫ (MonoidalClosed.pre (d l n)).app X

/-- The full abstract forward predicate equality is proved before any recursive
comparison or drop constructor is supplied. -/
theorem literalFunctionDropFormula_eq
    (source : CanonicalSourceSmash.SourceContext q (EnrichedFunctorCat V J))
    (P : ℕ → EnrichedFunctorCat V J) :
    letI := source.monoidalCategory
    letI := CanonicalSourceSmashClosed.Selected.monoidalClosed source
    ∀ (F : ∀ n : ℕ, ihom (P n) ≅ Functor.Iteration.iterate (ihom (P 1)) n)
      (d : (P 1 ⟶ 𝟙_ (EnrichedFunctorCat V J)) → ∀ n : ℕ, P (n + 1) ⟶ P n),
      LiteralFunctionDropFormula source P F d =
        (∀ l : P 1 ⟶ 𝟙_ (EnrichedFunctorCat V J),
          Powers.FullCompatibility.FunctionDrop (P 1) P F (d l) l) := by
  let := source.monoidalCategory
  let := CanonicalSourceSmashClosed.Selected.monoidalClosed source
  intro F d
  rfl

/-- The inverse equality retains the entire abstract function and drop families
instead of unfolding any chosen native or generic recursion. -/
theorem literalFunctionDropInverseFormula_eq
    (source : CanonicalSourceSmash.SourceContext q (EnrichedFunctorCat V J))
    (P : ℕ → EnrichedFunctorCat V J) :
    letI := source.monoidalCategory
    letI := CanonicalSourceSmashClosed.Selected.monoidalClosed source
    ∀ (F : ∀ n : ℕ, ihom (P n) ≅ Functor.Iteration.iterate (ihom (P 1)) n)
      (d : (P 1 ⟶ 𝟙_ (EnrichedFunctorCat V J)) → ∀ n : ℕ, P (n + 1) ⟶ P n),
      LiteralFunctionDropInverseFormula source P F d =
        (∀ l : P 1 ⟶ 𝟙_ (EnrichedFunctorCat V J),
          Powers.FullCompatibility.FunctionDropInverse (P 1) P F (d l) l) := by
  let := source.monoidalCategory
  let := CanonicalSourceSmashClosed.Selected.monoidalClosed source
  intro F d
  rfl

/-- The complete actual power-function forward square, with its source context bound once. -/
def LiteralPowerFunctionDropFormula (S : ℕ → V) (data : Data c S) : Prop :=
  let source := sourceContext c
  letI := source.monoidalCategory
  letI := CanonicalSourceSmashClosed.Selected.monoidalClosed source
  LiteralFunctionDropFormula source (object c S) (powerFunction c S data) (drop c S data)

/-- The complete actual power-function inverse square uses that same selected source. -/
def LiteralPowerFunctionDropInverseFormula (S : ℕ → V) (data : Data c S) : Prop :=
  let source := sourceContext c
  letI := source.monoidalCategory
  letI := CanonicalSourceSmashClosed.Selected.monoidalClosed source
  LiteralFunctionDropInverseFormula source (object c S) (powerFunction c S data) (drop c S data)

/-- Equality identifies the entire forward predicate before selecting any l, n or X. -/
theorem literalPowerFunctionDropFormula_eq (S : ℕ → V) (data : Data c S) :
    LiteralPowerFunctionDropFormula c S data = PowerFunctionDropCompatibility c S data :=
  literalFunctionDropFormula_eq (sourceContext c) (object c S)
    (powerFunction c S data) (drop c S data)

/-- Equality identifies the entire inverse predicate before any unit arrow or target is selected. -/
theorem literalPowerFunctionDropInverseFormula_eq (S : ℕ → V) (data : Data c S) :
    LiteralPowerFunctionDropInverseFormula c S data = PowerFunctionDropInverseCompatibility c S data :=
  literalFunctionDropInverseFormula_eq (sourceContext c) (object c S)
    (powerFunction c S data) (drop c S data)

end PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.TypedFullPowerData
end
end FullLiteralSourceFunctionPredicates
