/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.MappingParametrized

/-! # Public weighted-end variance and projection adjunction checks -/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uI uV vV

open CategoryTheory Limits Opposite MonoidalCategory
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed

namespace MathlibExtTest.MappingParametrized

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [EnrichedCategory V I]

example {M N : V} (i : M ⟶ N) {X Y : EnrichedFunctorCat V I} (f : X ⟶ Y) :
    ((EnrichedFunctorCat.tensorBifunctor (V := V) (A := I)).obj M).map f ≫
        ((EnrichedFunctorCat.tensorBifunctor (V := V) (A := I)).map i).app Y =
      ((EnrichedFunctorCat.tensorBifunctor (V := V) (A := I)).map i).app X ≫
        ((EnrichedFunctorCat.tensorBifunctor (V := V) (A := I)).obj N).map f :=
  scalarTensorMap_diagram_naturality i f

variable [HasProducts.{uI} V] [HasEqualizers V]

example (X Y : EnrichedFunctorCat V I) :
    ((WeightedEndVariance.bifunctor (V := V) (I := I)).obj (op X)).obj Y =
      WeightedEndVariance.object X Y := rfl

example {X X' : EnrichedFunctorCat V I} (j : X' ⟶ X)
    (Y : EnrichedFunctorCat V I) :
    ((WeightedEndVariance.bifunctor (V := V) (I := I)).map j.op).app Y =
      WeightedEndVariance.pre j Y := rfl

example {X Y Z : EnrichedFunctorCat V I} (j : X ⟶ Y) (k : Y ⟶ Z)
    (U : EnrichedFunctorCat V I) :
    ((WeightedEndVariance.bifunctor (V := V) (I := I)).map (j ≫ k).op).app U =
      ((WeightedEndVariance.bifunctor (V := V) (I := I)).map k.op).app U ≫
        ((WeightedEndVariance.bifunctor (V := V) (I := I)).map j.op).app U :=
  WeightedEndVariance.pre_comp j k U

example (X : EnrichedFunctorCat V I) {Y Z U : EnrichedFunctorCat V I}
    (p : Y ⟶ Z) (q : Z ⟶ U) :
    ((WeightedEndVariance.bifunctor (V := V) (I := I)).obj (op X)).map (p ≫ q) =
      ((WeightedEndVariance.bifunctor (V := V) (I := I)).obj (op X)).map p ≫
        ((WeightedEndVariance.bifunctor (V := V) (I := I)).obj (op X)).map q :=
  WeightedEndVariance.post_comp X p q

example {X X' Y Z : EnrichedFunctorCat V I} (j : X' ⟶ X) (p : Y ⟶ Z) :
    WeightedEndVariance.post X p ≫ WeightedEndVariance.pre j Z =
      WeightedEndVariance.pre j Y ≫ WeightedEndVariance.post X' p :=
  WeightedEndVariance.pre_post j p

example {X X' : EnrichedFunctorCat V I} (j : X' ⟶ X)
    (Y : EnrichedFunctorCat V I) (a : I) :
    WeightedEndVariance.pre j Y ≫ WeightedEndVariance.projection X' Y a =
      WeightedEndVariance.projection X Y a ≫
        (MonoidalClosed.pre (component j a)).app (Y.toEnrichedFunctor.obj a) :=
  WeightedEndVariance.pre_projection j Y a

example (X : EnrichedFunctorCat V I) {Y Z : EnrichedFunctorCat V I}
    (p : Y ⟶ Z) (a : I) :
    WeightedEndVariance.post X p ≫ WeightedEndVariance.projection X Z a =
      WeightedEndVariance.projection X Y a ≫
        (ihom (X.toEnrichedFunctor.obj a)).map (component p a) :=
  WeightedEndVariance.post_projection X p a

section ProjectionAdjunction

variable
  (adj : ∀ X : EnrichedFunctorCat V I,
    (WeightedEndVariance.tensorBifunctor (V := V) (I := I)).flip.obj X ⊣
      WeightedEndVariance.rightFunctor X)
  (E : ∀ (X Y : EnrichedFunctorCat V I) (T : V),
    (T ⟶ WeightedEndVariance.object X Y) ≃ (tensorLeftObject T X ⟶ Y))
  (hEq : ∀ X Y T, (adj X).homEquiv T Y = (E X Y T).symm)
  (hE : ∀ (X Y : EnrichedFunctorCat V I) (T : V)
    (f : tensorLeftObject T X ⟶ Y) (a : I),
    (E X Y T).symm f ≫ WeightedEndVariance.projection X Y a =
      MonoidalClosed.curry
        ((β_ T (X.toEnrichedFunctor.obj a)).inv ≫ component f a))

example : (WeightedEndVariance.tensorBifunctor (V := V) (I := I)).flip ⊣₂
    WeightedEndVariance.bifunctor :=
  WeightedEndVariance.parametrizedOfProjection adj E hEq hE

example (X : EnrichedFunctorCat V I) :
    (WeightedEndVariance.parametrizedOfProjection adj E hEq hE).adj X = adj X := rfl

example (X Y : EnrichedFunctorCat V I) (T : V) :
    (WeightedEndVariance.parametrizedOfProjection adj E hEq hE).homEquiv
      (X₁ := X) (X₂ := T) (X₃ := Y) = (E X Y T).symm :=
  hEq X Y T

example {X X' Y : EnrichedFunctorCat V I} (j : X' ⟶ X) (T : V)
    (f : tensorLeftObject T X ⟶ Y) :
    (E X' Y T).symm (tensorLeftMap T j ≫ f) =
      (E X Y T).symm f ≫ WeightedEndVariance.pre j Y :=
  WeightedEndVariance.inverse_source_of_projections E hE j T f

end ProjectionAdjunction

end MathlibExtTest.MappingParametrized
