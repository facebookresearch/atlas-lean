/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
MathlibExt.Topology.Category.TopCat.Embedding.TopCatHornCoproductClosedT1

@[expose] public section

/-!
# Horn-coproduct pushout closed-T1 clients

Thin public clients for
`TopCat.pushouts_coproducts_realizedHornInclusions_le_closedT1Embeddings` and
`TopCat.transfiniteCompositionsOfShape_pushouts_coproducts_horn_le_closedT1`
by term application only. Forwards the shape order premises unchanged.
Supplies no premise, adds no instance, and claims no coproduct inclusion,
small-object, factorization, or model structure.
-/

set_option autoImplicit false

open CategoryTheory

universe u

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.TopCatHornCoproductClosedT1Tests

/-- Pushout closure client, by direct term application. -/
theorem pushouts_coproducts_horn_le_closedT1_client :
    (CategoryTheory.MorphismProperty.coproducts.{u}
      (TopCat.realizedHornInclusions :
        CategoryTheory.MorphismProperty TopCat.{u})).pushouts ≤
      TopCat.closedT1Embeddings :=
  TopCat.pushouts_coproducts_realizedHornInclusions_le_closedT1Embeddings

/-- Shape-indexed transfinite closure client, forwarding order premises. -/
theorem transfiniteCompositionsOfShape_pushouts_coproducts_horn_le_closedT1_client
    {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J]
    [WellFoundedLT J] :
    CategoryTheory.MorphismProperty.transfiniteCompositionsOfShape
      (CategoryTheory.MorphismProperty.coproducts.{u}
        (TopCat.realizedHornInclusions :
          CategoryTheory.MorphismProperty TopCat.{u})).pushouts J ≤
      TopCat.closedT1Embeddings :=
  TopCat.transfiniteCompositionsOfShape_pushouts_coproducts_horn_le_closedT1

#print axioms TopCat.transfiniteCompositionsOfShape_pushouts_coproducts_horn_le_closedT1
#print axioms transfiniteCompositionsOfShape_pushouts_coproducts_horn_le_closedT1_client

end MathlibExtTest.AlgebraicTopology.ModelCategory.TopCatHornCoproductClosedT1Tests
