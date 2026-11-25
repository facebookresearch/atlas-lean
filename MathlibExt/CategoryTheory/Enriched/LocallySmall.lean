/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module
public import MathlibExt.CategoryTheory.Enriched.FunctorCategory
public import Mathlib.CategoryTheory.EssentiallySmall

@[expose] public section
set_option autoImplicit false
noncomputable section
universe w uA uV vV

namespace CategoryTheory.EnrichedFunctorCat

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]

/-- Genuine unit-graded transformations are small whenever their actual component family is. -/
instance locallySmall [Small.{w} A] [LocallySmall.{w} V] :
    LocallySmall.{w} (EnrichedFunctorCat V A) where
  hom_small F G := small_of_injective
    (f := fun t : F ⟶ G => fun a : A => component t a) (by
      intro f g h
      apply hom_ext
      intro a
      exact congrFun h a)

end CategoryTheory.EnrichedFunctorCat
