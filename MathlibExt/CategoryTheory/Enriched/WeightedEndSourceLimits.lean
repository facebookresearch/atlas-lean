/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex

module

public import MathlibExt.CategoryTheory.Adjunction.ParametrizedSourceLimits
public import MathlibExt.CategoryTheory.Enriched.ScalarTensorFunctorValue

/-!
# Source limits and Hom functions of an actual weighted end

All tensor and mapping functors are fixed before specialization of the
ambient closed category. The actual scalar adjunction is transported
through the entire original bifunctor equality. This supplies source
preservation without comparing its native constructor bodies again.

The parametrized adjunction's entire Hom family identifies both actual
source functions. Every original weight map and every scalar, source and
target endpoint remains explicit.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe uV vV uI w w'

open CategoryTheory CategoryTheory.Limits EnrichedFunctorCat Opposite
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedFunctorCat.WeightedEndSourceLimits

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [EnrichedCategory V I] [HasProducts.{uI} V] [HasEqualizers V]
  (adj : (WeightedEndVariance.tensorBifunctor (V := V) (I := I)).flip ⊣₂
    WeightedEndVariance.bifunctor (V := V) (I := I))

include adj in
/-- Actual scalar tensor/cotensor adjunctions, with the complete
weighted tensor functor fixed, give all source limit preservation. -/
theorem source_preservesLimitsOfSize (E : EnrichedFunctorCat V I) :
    PreservesLimitsOfSize.{w, w'} (WeightedEndVariance.bifunctor.flip.obj E) :=
  ParametrizedAdjunction.source_preservesLimitsOfSize adj
    (fun T => ScalarLeibniz.cotensorBifunctor.obj (op T))
    (fun T => ScalarTensorFunctorValue.weightedScalarAdjunction.adj T) E

include adj in
/-- The same fixed source functor carries the caller's original
pushout to the full actual mapping pullback with all four legs. -/
theorem sourceSquare
    {A B Z C : EnrichedFunctorCat V I} (i : A ⟶ B) (z : A ⟶ Z)
    (kB : B ⟶ C) (kZ : Z ⟶ C) (sq : IsPushout i z kB kZ)
    (E : EnrichedFunctorCat V I) :
    IsPullback (WeightedEndVariance.pre kB E) (WeightedEndVariance.pre kZ E)
      (WeightedEndVariance.pre i E) (WeightedEndVariance.pre z E) := by
  let _ : PreservesLimitsOfSize.{0, 0} (WeightedEndVariance.bifunctor.flip.obj E) :=
    source_preservesLimitsOfSize adj E
  exact (sq.op.map (WeightedEndVariance.bifunctor.flip.obj E)).flip

variable
  (e : ∀ X Y : EnrichedFunctorCat V I, ∀ T : V,
    (T ⟶ WeightedEndVariance.object X Y) ≃ (tensorLeftObject T X ⟶ Y))
  (hEquiv : ∀ X Y T, (adj.adj X).homEquiv T Y = (e X Y T).symm)

include hEquiv in
/-- The full inverse source function follows from the whole actual
Hom family equality and the original parametrized source naturality. -/
theorem inverse_source
    {A B : EnrichedFunctorCat V I} (f : A ⟶ B)
    (E : EnrichedFunctorCat V I) (T : V) (g : tensorLeftObject T B ⟶ E) :
    (e A E T).symm (tensorLeftMap T f ≫ g) =
      (e B E T).symm g ≫ WeightedEndVariance.pre f E := by
  have h := adj.homEquiv_naturality_one (X₂ := T) (X₃ := E) f g
  change (adj.adj A).homEquiv T E (tensorLeftMap T f ≫ g) =
    (adj.adj B).homEquiv T E g ≫ WeightedEndVariance.pre f E at h
  rw [hEquiv, hEquiv] at h
  exact h

include hEquiv in
/-- The full forward source function follows from the same original
inverse law, with every actual caller coefficient and target retained. -/
theorem forward_source
    {A B : EnrichedFunctorCat V I} (f : A ⟶ B)
    (E : EnrichedFunctorCat V I) (T : V)
    (h : T ⟶ WeightedEndVariance.object B E) :
    e A E T (h ≫ WeightedEndVariance.pre f E) =
      tensorLeftMap T f ≫ e B E T h := by
  have q := congrArg (e A E T) (inverse_source adj e hEquiv f E T (e B E T h))
  rw [Equiv.apply_symm_apply, Equiv.symm_apply_apply] at q
  exact q.symm

include hEquiv in
/-- Every original source arrow has the same entire inverse Hom
function before a scalar or native target is selected. -/
theorem inverse_source_function
    {A B : EnrichedFunctorCat V I} (f : A ⟶ B)
    (E : EnrichedFunctorCat V I) (T : V) :
    (fun g => (e A E T).symm (tensorLeftMap T f ≫ g)) =
      fun g => (e B E T).symm g ≫ WeightedEndVariance.pre f E := by
  funext g
  exact inverse_source adj e hEquiv f E T g

include hEquiv in
/-- Every original source arrow also has the same entire forward
Hom function; both functions retain the actual chosen end maps. -/
theorem forward_source_function
    {A B : EnrichedFunctorCat V I} (f : A ⟶ B)
    (E : EnrichedFunctorCat V I) (T : V) :
    (fun h => e A E T (h ≫ WeightedEndVariance.pre f E)) =
      fun h => tensorLeftMap T f ≫ e B E T h := by
  funext h
  exact forward_source adj e hEquiv f E T h

end CategoryTheory.EnrichedFunctorCat.WeightedEndSourceLimits
