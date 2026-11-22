/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.PointedCGWH.NativeParametrizedCharacteristics
public import Mathlib.CategoryTheory.Adjunction.Parametrized
public import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Tensor and mapping corners of native enriched diagrams

The native mapping corner is the specified pullback of source-precomposition and
target-postcomposition maps on weighted ends, with both projection equations. Tensor and
mapping corners have naturally equivalent Arrow Hom sets. This equivalence identifies their
full lifting properties for every supplied pushout and pullback corner.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section

universe u v
open CategoryTheory CategoryTheory.Limits EnrichedFunctorCat
open scoped MonoidalClosed

namespace PointedCGWH.NativeMappingCorner

open PointedCGWH.EnrichedFunctorMapping
attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf
variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]

/-- The whole original mapping corner is the actual pullback of source and target maps. -/
def square {F G X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (j : F ⟶ G) (p : X ⟶ Y) :
    WeightedEndVariance.bifunctor.PullbackObjObj j p :=
  Functor.PullbackObjObj.ofHasPullback WeightedEndVariance.bifunctor j p

/-- The actual first mapping-corner projection retains the original source map. -/
theorem square_first {F G X Y : EnrichedFunctorCat PointedCGWH.{u, v} I}
    (j : F ⟶ G) (p : X ⟶ Y) :
    (square j p).π ≫ (square j p).fst = Enriched.weightedEnd.mapWeight G.toEnrichedFunctor
      X.toEnrichedFunctor F.toEnrichedFunctor j :=
  (square j p).π_fst

/-- The actual second mapping-corner projection retains the original target map. -/
theorem square_second {F G X Y : EnrichedFunctorCat PointedCGWH.{u, v} I}
    (j : F ⟶ G) (p : X ⟶ Y) :
    (square j p).π ≫ (square j p).snd = WeightedEndVariance.post G p := (square j p).π_snd

/-- Both full native corner maps are related by the actual original Arrow Hom equivalence. -/
def arrowHomEquiv
    {F G X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} {j : F ⟶ G} {p : X ⟶ Y}
    {M N : PointedCGWH.{u, v}} {i : M ⟶ N}
    (po : WeightedEndVariance.tensorBifunctor.PushoutObjObj i j)
    (pb : WeightedEndVariance.bifunctor.PullbackObjObj j p) :
    (Arrow.mk po.ι ⟶ Arrow.mk p) ≃ (Arrow.mk i ⟶ Arrow.mk pb.π) :=
  NativeOriginalParametrizedMapping.adjunction.arrowHomEquiv po.flip pb

/-- The same original pushout and pullback arrows have exactly equivalent lifting properties. -/
theorem lifting_iff
    {F G X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} {j : F ⟶ G} {p : X ⟶ Y}
    {M N : PointedCGWH.{u, v}} {i : M ⟶ N}
    (po : WeightedEndVariance.tensorBifunctor.PushoutObjObj i j)
    (pb : WeightedEndVariance.bifunctor.PullbackObjObj j p) :
    HasLiftingProperty po.ι p ↔ HasLiftingProperty i pb.π :=
  NativeOriginalParametrizedMapping.adjunction.hasLiftingProperty_iff po.flip pb

end PointedCGWH.NativeMappingCorner
