/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatGenerators
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition

/-!
# Closed T1-embeddings from horn-cell attachments

Realized simplicial horn inclusions are closed T1-embeddings. Coproducts and their pushouts
retain that property, as do transfinite compositions along a bottomed well-founded linear
successor order.

A closed T1-embedding is a closed embedding with closed codomain singletons outside its image.
Spaces and the composition shape use an arbitrary universe u.
-/

@[expose] public section

universe u

open CategoryTheory MorphismProperty

namespace TopCat

/-- In TopCat.{u}, every coproduct of realized simplicial horn inclusions is a closed embedding with
closed codomain singletons outside its image. -/
theorem coproducts_realizedHornInclusions_le_closedT1Embeddings :
    coproducts.{u} (realizedHornInclusions : MorphismProperty TopCat.{u}) ≤
      closedT1Embeddings :=
  coproducts_le_iff.mpr realizedHornInclusions_le_closedT1Embeddings

/-- Every pushout of a coproduct of realized horn inclusions is a closed T1-embedding in TopCat.{u}.
The codomain singleton of every point outside the image is closed. -/
theorem pushouts_coproducts_realizedHornInclusions_le_closedT1Embeddings :
    (coproducts.{u} (realizedHornInclusions : MorphismProperty TopCat.{u})).pushouts ≤
      closedT1Embeddings :=
  pushouts_le_iff.mpr coproducts_realizedHornInclusions_le_closedT1Embeddings

variable {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J]
  [WellFoundedLT J]

/-- Let J:Type u be a bottomed well-founded linear successor order. Transfinite compositions of
shape J of horn-coproduct pushouts are closed T1-embeddings. The codomain singleton of every
point outside the image is closed. -/
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
