/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.SphereOperatorCategory

@[expose] public section

set_option autoImplicit false
noncomputable section

universe uV vV uI vI

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonoidalClosed

namespace CategoryTheory.Enriched.SphereOperator

open Limits

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
  (L : EnrichedFunctor.LaxMonoidalData d
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
  [∀ n m : I, HasCoproduct (weightedCoend.relations (weight d n m) S)]
  [∀ n m : I, HasCoproduct (weightedCoend.objects (weight d n m) S)]
  [∀ n m : I, HasCoequalizer (weightedCoend.leftMap (weight d n m) S)
    (weightedCoend.rightMap (weight d n m) S)]

-- The tag determines the actual enrichment; no category structure is supplied.
example : EnrichedCategory V (OperatorIndex d S L) := inferInstance

-- The source objects have their actual operator enrichment and can therefore
-- be used by genuine enriched functors, independently of the old enrichment on I.
example (F : EnrichedFunctor V (OperatorIndex d S L) V)
    (x : OperatorIndex d S L) :
    identityGenerator d S L x.asIndex ≫ F.map x x = eId V (F.obj x) := by
  simpa only [operatorIndex_id] using F.map_id x

end CategoryTheory.Enriched.SphereOperator
