/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Enriched.ScalarTensor
import Mathlib.CategoryTheory.Adjunction.Parametrized
public import MathlibExt.CategoryTheory.Enriched.Limits.WeightedEnd

/-!
# Actual full weighted-end variance and source transpose

All end objects, source maps, target maps and projections are the original
ones. Generic proofs keep ambient category/closed data abstract. A supplied
actual projection formula identifies source transpose without assuming an
adjunction, equivalence, lifting condition or model compatibility.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uI uV vV

open CategoryTheory Limits Opposite MonoidalCategory BraidedCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedFunctorCat.WeightedEndVariance

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [EnrichedCategory V I] [HasProducts.{uI} V] [HasEqualizers V]

/-- The full actual chosen original weighted end. -/
abbrev object (X Y : EnrichedFunctorCat V I) : V :=
  Enriched.weightedEnd X.toEnrichedFunctor Y.toEnrichedFunctor

/-- Each actual projection retains the original full internal Hom. -/
abbrev projection (X Y : EnrichedFunctorCat V I) (a : I) :
    object X Y ⟶ (ihom (X.toEnrichedFunctor.obj a)).obj (Y.toEnrichedFunctor.obj a) :=
  Enriched.weightedEnd.π X.toEnrichedFunctor Y.toEnrichedFunctor a

/-- Actual source variance is the original full weighted-end weight map. -/
def pre {X X' : EnrichedFunctorCat V I} (j : X' ⟶ X) (Y : EnrichedFunctorCat V I) :
    object X Y ⟶ object X' Y :=
  Enriched.weightedEnd.mapWeight X.toEnrichedFunctor Y.toEnrichedFunctor
    X'.toEnrichedFunctor j

/-- Actual target variance is the original full weighted-end diagram map. -/
def post (X : EnrichedFunctorCat V I) {Y Z : EnrichedFunctorCat V I} (p : Y ⟶ Z) :
    object X Y ⟶ object X Z :=
  Enriched.weightedEnd.mapDiagram X.toEnrichedFunctor Y.toEnrichedFunctor
    Z.toEnrichedFunctor p

/-- Every original source projection uses literal internal-Hom precomposition. -/
theorem pre_projection {X X' : EnrichedFunctorCat V I}
    (j : X' ⟶ X) (Y : EnrichedFunctorCat V I) (a : I) :
    pre j Y ≫ projection X' Y a =
      projection X Y a ≫ (MonoidalClosed.pre (component j a)).app
        (Y.toEnrichedFunctor.obj a) :=
  Enriched.weightedEnd.mapWeight_π X.toEnrichedFunctor Y.toEnrichedFunctor
    X'.toEnrichedFunctor j a

/-- Every original target projection uses literal internal-Hom postcomposition. -/
theorem post_projection (X : EnrichedFunctorCat V I)
    {Y Z : EnrichedFunctorCat V I} (p : Y ⟶ Z) (a : I) :
    post X p ≫ projection X Z a =
      projection X Y a ≫ (ihom (X.toEnrichedFunctor.obj a)).map (component p a) :=
  Enriched.weightedEnd.mapDiagram_π X.toEnrichedFunctor Y.toEnrichedFunctor
    Z.toEnrichedFunctor p a

/-- Source variance preserves the original identity. -/
theorem pre_id (X Y : EnrichedFunctorCat V I) : pre (𝟙 X) Y = 𝟙 (object X Y) :=
  Enriched.weightedEnd.mapWeight_id X.toEnrichedFunctor Y.toEnrichedFunctor

/-- Target variance preserves the original identity. -/
theorem post_id (X Y : EnrichedFunctorCat V I) : post X (𝟙 Y) = 𝟙 (object X Y) :=
  Enriched.weightedEnd.mapDiagram_id X.toEnrichedFunctor Y.toEnrichedFunctor

/-- Source composition keeps the complete original contravariant order. -/
theorem pre_comp {X Y Z : EnrichedFunctorCat V I} (j : X ⟶ Y) (k : Y ⟶ Z)
    (U : EnrichedFunctorCat V I) : pre (j ≫ k) U = pre k U ≫ pre j U :=
  (Enriched.weightedEnd.mapWeight_comp Z.toEnrichedFunctor U.toEnrichedFunctor
    Y.toEnrichedFunctor X.toEnrichedFunctor k j).symm

/-- Target composition keeps both original full diagram maps. -/
theorem post_comp (X : EnrichedFunctorCat V I) {Y Z U : EnrichedFunctorCat V I}
    (p : Y ⟶ Z) (q : Z ⟶ U) : post X (p ≫ q) = post X p ≫ post X q :=
  (Enriched.weightedEnd.mapDiagram_comp X.toEnrichedFunctor Y.toEnrichedFunctor
    Z.toEnrichedFunctor U.toEnrichedFunctor p q).symm

/-- Full source and target maps commute on the entire original chosen end. -/
theorem pre_post {X X' Y Z : EnrichedFunctorCat V I}
    (j : X' ⟶ X) (p : Y ⟶ Z) : post X p ≫ pre j Z = pre j Y ≫ post X' p := by
  apply Enriched.weightedEnd.hom_ext X'.toEnrichedFunctor Z.toEnrichedFunctor
  intro a
  let preY := (MonoidalClosed.pre (component j a)).app (Y.toEnrichedFunctor.obj a)
  let preZ := (MonoidalClosed.pre (component j a)).app (Z.toEnrichedFunctor.obj a)
  let postX := (ihom (X.toEnrichedFunctor.obj a)).map (component p a)
  let postX' := (ihom (X'.toEnrichedFunctor.obj a)).map (component p a)
  have hL : (post X p ≫ pre j Z) ≫ projection X' Z a =
      projection X Y a ≫ postX ≫ preZ := by
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun q => post X p ≫ q) (pre_projection j Z a)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun q => q ≫ preZ) (post_projection X p a)).trans
            (Category.assoc _ _ _))))
  have hR : (pre j Y ≫ post X' p) ≫ projection X' Z a =
      projection X Y a ≫ preY ≫ postX' := by
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun q => pre j Y ≫ q) (post_projection X' p a)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun q => q ≫ postX') (pre_projection j Y a)).trans
            (Category.assoc _ _ _))))
  exact hL.trans
    ((congrArg (fun q => projection X Y a ≫ q)
      ((MonoidalClosed.pre (component j a)).naturality (component p a))).trans hR.symm)

/-- The full original target mapping functor. -/
def rightFunctor (X : EnrichedFunctorCat V I) : EnrichedFunctorCat V I ⥤ V where
  obj Y := object X Y
  map p := post X p
  map_id Y := post_id X Y
  map_comp p q := post_comp X p q

/-- Full original weighted ends with all original source/target variance. -/
def bifunctor : (EnrichedFunctorCat V I)ᵒᵖ ⥤ EnrichedFunctorCat V I ⥤ V where
  obj X := rightFunctor X.unop
  map j :=
    { app Y := pre j.unop Y
      naturality _ _ p := pre_post j.unop p }
  map_id X := by
    apply NatTrans.ext
    funext Y
    exact pre_id X.unop Y
  map_comp j k := by
    apply NatTrans.ext
    funext Y
    exact pre_comp k.unop j.unop Y

/-- Actual projection formulas derive complete source transpose.
The two maps are supplied as actual maps with literal projection equations. -/
theorem sourceTranspose {X X' Y : EnrichedFunctorCat V I} (j : X' ⟶ X) (T : V)
    (f : tensorLeftObject T X ⟶ Y) (h : T ⟶ object X Y) (h' : T ⟶ object X' Y)
    (hh : ∀ a, h ≫ projection X Y a =
      MonoidalClosed.curry ((β_ T (X.toEnrichedFunctor.obj a)).inv ≫ component f a))
    (hh' : ∀ a, h' ≫ projection X' Y a =
      MonoidalClosed.curry ((β_ T (X'.toEnrichedFunctor.obj a)).inv ≫
        component (tensorLeftMap T j ≫ f) a)) :
    h' = h ≫ pre j Y := by
  apply Enriched.weightedEnd.hom_ext X'.toEnrichedFunctor Y.toEnrichedFunctor
  intro a
  rw [hh', component_comp, tensorLeftMap_component,
    Category.assoc, pre_projection, ← Category.assoc, hh, MonoidalClosed.curry_pre_app]
  apply congrArg MonoidalClosed.curry
  change (β_ T (X'.toEnrichedFunctor.obj a)).inv ≫ (T ◁ component j a) ≫ component f a =
    (component j a ▷ T) ≫ (β_ T (X.toEnrichedFunctor.obj a)).inv ≫ component f a
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun q => q ≫ component f a)
      (braiding_inv_naturality_left (component j a) T).symm).trans (Category.assoc _ _ _))

end CategoryTheory.EnrichedFunctorCat.WeightedEndVariance
