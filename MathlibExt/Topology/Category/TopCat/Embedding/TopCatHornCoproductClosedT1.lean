/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatGenerators
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition

/-!
# Horn coproduct pushouts as closed T1-embeddings in `TopCat`

This file is part of the KQ3 layer. It composes the accepted horn bound
`TopCat.realizedHornInclusions_le_closedT1Embeddings` with the accepted
closed T1-embedding stability package (coproducts, pushouts, transfinite
composition). No geometric proof is restated and no small-object,
factorization, weak-equivalence, or model-structure claim is made here.
The shape-indexed closure feeds both omega-small and actual-cardinal
horn-cell closures.
-/

@[expose] public section

universe u

open CategoryTheory MorphismProperty

namespace TopCat

/-- Coproducts of realized horn inclusions are closed T1-embeddings. -/
theorem coproducts_realizedHornInclusions_le_closedT1Embeddings :
    coproducts.{u} (realizedHornInclusions : MorphismProperty TopCat.{u}) ≤
      closedT1Embeddings :=
  coproducts_le_iff.mpr realizedHornInclusions_le_closedT1Embeddings

/-- Pushouts of horn coproducts are closed T1-embeddings. -/
theorem pushouts_coproducts_realizedHornInclusions_le_closedT1Embeddings :
    (coproducts.{u} (realizedHornInclusions : MorphismProperty TopCat.{u})).pushouts ≤
      closedT1Embeddings :=
  pushouts_le_iff.mpr coproducts_realizedHornInclusions_le_closedT1Embeddings

variable {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J]
  [WellFoundedLT J]

/-- Transfinite compositions of horn-coproduct pushouts are closed T1-embeddings. -/
theorem transfiniteCompositionsOfShape_pushouts_coproducts_horn_le_closedT1 :
    transfiniteCompositionsOfShape
        (coproducts.{u} (realizedHornInclusions : MorphismProperty TopCat.{u})).pushouts
        J ≤
      closedT1Embeddings := by
  calc _ ≤ transfiniteCompositionsOfShape closedT1Embeddings.{u} J :=
        transfiniteCompositionsOfShape_monotone J
          pushouts_coproducts_realizedHornInclusions_le_closedT1Embeddings
    _ ≤ closedT1Embeddings :=
        transfiniteCompositionsOfShape_le (W := closedT1Embeddings.{u}) (J := J)

end TopCat
