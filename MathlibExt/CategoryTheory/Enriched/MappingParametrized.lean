/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.WeightedEndVariance
public import MathlibExt.CategoryTheory.Enriched.ScalarTensorBifunctor
import Mathlib.CategoryTheory.Adjunction.Parametrized

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section

universe uI uV vV
open CategoryTheory CategoryTheory.Limits MonoidalCategory BraidedCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedFunctorCat.WeightedEndVariance

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V] {I : Type uI} [EnrichedCategory V I]

/-- Reuse scalar tensoring with every actual coefficient and diagram map. -/
abbrev tensorBifunctor : V ⥤ EnrichedFunctorCat V I ⥤ EnrichedFunctorCat V I :=
  EnrichedFunctorCat.tensorBifunctor (V := V) (A := I)

variable [HasProducts.{uI} V] [HasEqualizers V]

/-- Source transpose is obtained from both actual inverse projection equations. -/
theorem inverse_source_of_projections
    (E : ∀ (X Y : EnrichedFunctorCat V I) (T : V),
      (T ⟶ object X Y) ≃ (tensorLeftObject T X ⟶ Y))
    (hE : ∀ (X Y : EnrichedFunctorCat V I) (T : V)
      (f : tensorLeftObject T X ⟶ Y) (a : I),
      (E X Y T).symm f ≫ projection X Y a =
        MonoidalClosed.curry
          ((β_ T (X.toEnrichedFunctor.obj a)).inv ≫ component f a))
    {X X' Y : EnrichedFunctorCat V I} (j : X' ⟶ X) (T : V)
    (f : tensorLeftObject T X ⟶ Y) :
    (E X' Y T).symm (tensorLeftMap T j ≫ f) = (E X Y T).symm f ≫ pre j Y :=
  sourceTranspose j T f ((E X Y T).symm f)
    ((E X' Y T).symm (tensorLeftMap T j ≫ f))
    (hE X Y T f) (hE X' Y T (tensorLeftMap T j ≫ f))

/-- Complete original adjunctions and their actual Hom values give parameter naturality. -/
def parametrizedOfProjection
    (adj : ∀ X : EnrichedFunctorCat V I, (tensorBifunctor (V := V) (I := I)).flip.obj X ⊣
      rightFunctor X)
    (E : ∀ (X Y : EnrichedFunctorCat V I) (T : V),
      (T ⟶ object X Y) ≃ (tensorLeftObject T X ⟶ Y))
    (hEq : ∀ X Y T, (adj X).homEquiv T Y = (E X Y T).symm)
    (hE : ∀ (X Y : EnrichedFunctorCat V I) (T : V)
      (f : tensorLeftObject T X ⟶ Y) (a : I),
      (E X Y T).symm f ≫ projection X Y a =
        MonoidalClosed.curry
          ((β_ T (X.toEnrichedFunctor.obj a)).inv ≫ component f a)) :
    (tensorBifunctor (V := V) (I := I)).flip ⊣₂ bifunctor :=
  ParametrizedAdjunction.mk' adj (by
    intro X X' j T Y f
    change (adj X).homEquiv T Y (tensorLeftMap T j ≫ f) =
      (adj X').homEquiv T Y f ≫ pre j Y
    rw [hEq, hEq]
    exact inverse_source_of_projections E hE j T f)

end CategoryTheory.EnrichedFunctorCat.WeightedEndVariance
