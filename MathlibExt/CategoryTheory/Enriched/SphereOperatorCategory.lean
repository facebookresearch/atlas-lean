/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.SphereOperatorCategoryUnits
public import MathlibExt.CategoryTheory.Enriched.SphereOperatorAssociativity

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

/-- Tag only the index objects by the actual coefficient construction.
The original enrichment on I remains the one used to construct the weight.
The data tags make the derived operator enrichment a determined instance. -/
structure OperatorIndex
    (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
    (L : EnrichedFunctor.LaxMonoidalData d
      (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S) where
  /-- The object in the original index category. -/
  asIndex : I

variable (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
  (L : EnrichedFunctor.LaxMonoidalData d
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
  [∀ n m : I, HasCoproduct (weightedCoend.relations (weight d n m) S)]
  [∀ n m : I, HasCoproduct (weightedCoend.objects (weight d n m) S)]
  [∀ n m : I, HasCoequalizer (weightedCoend.leftMap (weight d n m) S)
    (weightedCoend.rightMap (weight d n m) S)]

/-- The genuine operator enrichment uses the original full coend Hom, original
identity and composition. Every law is derived from the proved coend equations;
no category dictionary or operator unit/associativity law is an input. -/
instance operatorEnrichedCategory : EnrichedCategory V (OperatorIndex d S L) where
  Hom x y := CategoryTheory.Enriched.SphereOperator.Hom d S x.asIndex y.asIndex
  id x := identityGenerator d S L x.asIndex
  comp x y z := composition d S L x.asIndex y.asIndex z.asIndex
  id_comp x y := by
    exact identity_comp_field d S L x.asIndex y.asIndex
  comp_id x y := by
    exact comp_identity_field d S L x.asIndex y.asIndex
  assoc w x y z := by
    exact composition_assoc d S L w.asIndex x.asIndex y.asIndex z.asIndex

/-- The operator Hom object is the literal original coend, with no presentation
or comparison carrier inserted. -/
@[simp] theorem operatorIndex_hom (x y : OperatorIndex d S L) :
    (x ⟶[V] y) = Hom d S x.asIndex y.asIndex := rfl

/-- The enriched identity is the original coefficient-unit generator. -/
@[simp] theorem operatorIndex_id (x : OperatorIndex d S L) :
    eId V x = identityGenerator d S L x.asIndex := rfl

/-- The enriched composition is the original two-coend descent. -/
@[simp] theorem operatorIndex_comp (x y z : OperatorIndex d S L) :
    eComp V x y z = composition d S L x.asIndex y.asIndex z.asIndex := rfl

end CategoryTheory.Enriched.SphereOperator
