/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.BraidingMonoidal
public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.LaxMonoidBraiding

/-!
# Commutative monoids from original enriched braided tensorators

The monoid and the symmetric Day category are both constructed from the
original source data and colimits. The full coend multiplication invariance
proves the stock commutative-monoid predicate on that same object.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uV vV uI vI
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedDayKernel.LaxMonoid

attribute [local instance] Enriched.prodCategory ColimitMonoidal.smallestColimits

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]
  [EnrichedOrdinaryCategory V I] [HasColimitsOfSize.{uI, uI} V]
  (d : EnrichedMonoidalCategoryData V I)
  (b : EnrichedBraidedMonoidalCategoryData V I d)
  (S : EnrichedFunctor V I V)
  (L : EnrichedFunctor.LaxMonoidalData d
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
  (B : EnrichedFunctor.LaxBraidedData L)

include B in
/-- The constructed monoid on the original object is commutative under the actual Day braid. -/
theorem isCommMonObj :
    letI := ColimitMonoidal.monoidalCategory d
    letI := BraidingMonoidal.symmetricCategory d b
    letI := monObj d S L
    IsCommMonObj (⟨S⟩ : EnrichedFunctorCat V I) := by
  let := ColimitMonoidal.monoidalCategory d
  let := BraidingMonoidal.symmetricCategory d b
  let := monObj d S L
  constructor
  exact multiply_braid d b S L B

include B in
/-- The stock multiplication of the constructed original monoid satisfies whole commutativity. -/
theorem monObj_mul_comm :
    letI := ColimitMonoidal.monoidalCategory d
    letI := BraidingMonoidal.symmetricCategory d b
    letI := monObj d S L
    (β_ (⟨S⟩ : EnrichedFunctorCat V I) ⟨S⟩).hom ≫
      MonObj.mul (X := (⟨S⟩ : EnrichedFunctorCat V I)) = MonObj.mul := by
  let := ColimitMonoidal.monoidalCategory d
  let := BraidingMonoidal.symmetricCategory d b
  let := monObj d S L
  let := isCommMonObj d b S L B
  exact IsCommMonObj.mul_comm (⟨S⟩ : EnrichedFunctorCat V I)

end CategoryTheory.EnrichedDayKernel.LaxMonoid
