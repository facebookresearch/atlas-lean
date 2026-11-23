/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatWeakHomotopyTransfiniteClosed

@[expose] public section

/-!
# Conditional transfinite closed-T1 stability client

Thin public client for
`TopCat.weakHomotopyEquivalences.of_transfiniteComposition_closedT1` by term
application only. Accepts the same explicit `SSet.KanComplex.W` stability
hypothesis and invokes the provider's conditional inclusion. Supplies no
premise, adds no instance, and claims no unconditional coproduct, pushout,
transfinite stability, or model structure.
-/

set_option autoImplicit false

open CategoryTheory Limits

universe v u

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.TopCatWeakHomotopyTransfiniteClosedTests

/-- Conditional client for the closed-T1 transfinite inclusion. -/
theorem of_closedT1_client {J : Type v} [LinearOrder J] [OrderBot J]
    [SuccOrder J] [WellFoundedLT J] {X Y : TopCat.{0}} {f : X ⟶ Y}
    (hf : (TopCat.weakHomotopyEquivalences ⊓
      TopCat.closedT1Embeddings).TransfiniteCompositionOfShape J f)
    [(SSet.KanComplex.W :
      MorphismProperty SSet.{0}).IsStableUnderTransfiniteCompositionOfShape J] :
    TopCat.weakHomotopyEquivalences f :=
  TopCat.weakHomotopyEquivalences.of_transfiniteComposition_closedT1 hf

/-- Closed-T1 transfinite weak closure with independent shape/ambient universes. -/
theorem transfiniteClosed_symbolic
    {J : Type v} [LinearOrder J] [OrderBot J] [SuccOrder J]
    [WellFoundedLT J] {X Y : TopCat.{u}} {f : X ⟶ Y}
    (hf : (TopCat.weakHomotopyEquivalences.{u} ⊓
      TopCat.closedT1Embeddings.{u}).TransfiniteCompositionOfShape J f)
    [MorphismProperty.IsStableUnderTransfiniteCompositionOfShape
      (SSet.KanComplex.W : MorphismProperty SSet.{u}) J] :
    TopCat.weakHomotopyEquivalences.{u} f :=
  TopCat.weakHomotopyEquivalences.of_transfiniteComposition_closedT1 hf

/-- Concrete universe-one closed-T1 transfinite weak closure. -/
theorem transfiniteClosed_u1
    {J : Type 1} [LinearOrder J] [OrderBot J] [SuccOrder J]
    [WellFoundedLT J] {X Y : TopCat.{1}} {f : X ⟶ Y}
    (hf : (TopCat.weakHomotopyEquivalences.{1} ⊓
      TopCat.closedT1Embeddings.{1}).TransfiniteCompositionOfShape J f)
    [MorphismProperty.IsStableUnderTransfiniteCompositionOfShape
      (SSet.KanComplex.W : MorphismProperty SSet.{1}) J] :
    TopCat.weakHomotopyEquivalences.{1} f :=
  TopCat.weakHomotopyEquivalences.of_transfiniteComposition_closedT1 hf

#print axioms TopCat.weakHomotopyEquivalences.of_transfiniteComposition_closedT1
#print axioms of_closedT1_client

end MathlibExtTest.AlgebraicTopology.ModelCategory.TopCatWeakHomotopyTransfiniteClosedTests
