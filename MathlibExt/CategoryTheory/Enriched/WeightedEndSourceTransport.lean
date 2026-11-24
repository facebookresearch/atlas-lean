/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex

module

public import MathlibExt.CategoryTheory.Enriched.WeightedEndSourceLimits

/-!
# Source preservation through the entire original source function equality

The equality of the complete source-functor function is eliminated while
the category and tensor/end data are still abstract. Preservation then
follows directly from the original tensor adjunctions. No separately
provided source-preservation proof family is a premise of this constructor.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe uV vV uI w w'

open CategoryTheory CategoryTheory.Limits EnrichedFunctorCat Opposite
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedFunctorCat.WeightedEndSourceTransport

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [EnrichedCategory V I] [HasProducts.{uI} V] [HasEqualizers V]
  (adj : (WeightedEndVariance.tensorBifunctor (V := V) (I := I)).flip ⊣₂
    WeightedEndVariance.bifunctor (V := V) (I := I))
  (S : EnrichedFunctorCat V I → (EnrichedFunctorCat V I)ᵒᵖ ⥤ V)
  (hS : S = fun E => (WeightedEndVariance.bifunctor (V := V) (I := I)).flip.obj E)

include adj hS in
/-- The same original source family preserves all source limits,
derived after its entire original functor function is identified. -/
theorem source_preservesLimitsOfSize :
    ∀ E, PreservesLimitsOfSize.{w, w'} (S E) := by
  cases hS
  exact fun E => WeightedEndSourceLimits.source_preservesLimitsOfSize adj E

end CategoryTheory.EnrichedFunctorCat.WeightedEndSourceTransport
