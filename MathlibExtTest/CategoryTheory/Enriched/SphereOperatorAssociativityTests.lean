/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

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
  (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
  (L : EnrichedFunctor.LaxMonoidalData d
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
  (n m k l : I)
  [HasCoproduct (weightedCoend.relations (weight d n m) S)]
  [HasCoproduct (weightedCoend.objects (weight d n m) S)]
  [HasCoequalizer (weightedCoend.leftMap (weight d n m) S)
    (weightedCoend.rightMap (weight d n m) S)]
  [HasCoproduct (weightedCoend.relations (weight d m k) S)]
  [HasCoproduct (weightedCoend.objects (weight d m k) S)]
  [HasCoequalizer (weightedCoend.leftMap (weight d m k) S)
    (weightedCoend.rightMap (weight d m k) S)]
  [HasCoproduct (weightedCoend.relations (weight d k l) S)]
  [HasCoproduct (weightedCoend.objects (weight d k l) S)]
  [HasCoequalizer (weightedCoend.leftMap (weight d k l) S)
    (weightedCoend.rightMap (weight d k l) S)]
  [HasCoproduct (weightedCoend.relations (weight d n k) S)]
  [HasCoproduct (weightedCoend.objects (weight d n k) S)]
  [HasCoequalizer (weightedCoend.leftMap (weight d n k) S)
    (weightedCoend.rightMap (weight d n k) S)]
  [HasCoproduct (weightedCoend.relations (weight d m l) S)]
  [HasCoproduct (weightedCoend.objects (weight d m l) S)]
  [HasCoequalizer (weightedCoend.leftMap (weight d m l) S)
    (weightedCoend.rightMap (weight d m l) S)]
  [HasCoproduct (weightedCoend.relations (weight d n l) S)]
  [HasCoproduct (weightedCoend.objects (weight d n l) S)]
  [HasCoequalizer (weightedCoend.leftMap (weight d n l) S)
    (weightedCoend.rightMap (weight d n l) S)]

#check composition_generator_assoc

-- This is the actual Mathlib EnrichedCategory.assoc field shape, on the
-- three entire coend Hom objects and independent source/target universes.
example :
    (α_ (Hom d S n m) (Hom d S m k) (Hom d S k l)).inv ≫
        (composition d S L n m k ▷ Hom d S k l) ≫
        composition d S L n k l =
      (Hom d S n m ◁ composition d S L m k l) ≫
        composition d S L n m l :=
  composition_assoc d S L n m k l

end CategoryTheory.Enriched.SphereOperator
