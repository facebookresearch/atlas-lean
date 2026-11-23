/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.TopCatRealizedCellClosedEmbedding

/-!
# Realized-cell closed-embedding clients

Thin direct clients for `TopCat.realizedGenerators_le_closedEmbeddings` and
`TopCat.relativeCellComplex_mem_closedEmbeddings`: the generator union lies in
closed embeddings, and any relative cell complex built from those generators is
a closed embedding. Also thin clients for the closed-T1 coproduct, pushout,
transfinite, and relative-cell theorems. Direct term application only; no new
proof, and no small-object, factorization, model-structure, or
weak-equivalence claim.
-/

@[expose] public section

set_option autoImplicit false

universe u u_1

namespace MathlibExtTest.AlgebraicTopology.ModelCategory
namespace TopCatRealizedCellClosedEmbeddingTests

theorem realizedGenerators_le_closedEmbeddings_client :
    (TopCat.realizedBoundaryInclusions ⊔ TopCat.realizedHornInclusions :
      CategoryTheory.MorphismProperty TopCat.{u}) ≤ TopCat.closedEmbeddings :=
  TopCat.realizedGenerators_le_closedEmbeddings

theorem relativeCellComplex_mem_closedEmbeddings_client
    {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J]
    [WellFoundedLT J]
    {α : J → Type*} {A B : (j : J) → α j → TopCat.{u}}
    {X Y : TopCat.{u}} {f : X ⟶ Y}
    (basicCell : (j : J) → (i : α j) → A j i ⟶ B j i)
    (c : HomotopicalAlgebra.RelativeCellComplex.{u} basicCell f)
    (hc : ∀ s : c.Cells, (TopCat.realizedBoundaryInclusions ⊔
      TopCat.realizedHornInclusions :
      CategoryTheory.MorphismProperty TopCat.{u}) (basicCell s.j s.i)) :
    TopCat.closedEmbeddings f :=
  TopCat.relativeCellComplex_mem_closedEmbeddings basicCell c hc

theorem coproducts_realizedGenerators_le_closedT1Embeddings_client :
    CategoryTheory.MorphismProperty.coproducts.{u}
      (TopCat.realizedBoundaryInclusions ⊔ TopCat.realizedHornInclusions :
        CategoryTheory.MorphismProperty TopCat.{u}) ≤
      TopCat.closedT1Embeddings :=
  TopCat.coproducts_realizedGenerators_le_closedT1Embeddings

theorem pushouts_coproducts_realizedGenerators_le_closedT1Embeddings_client :
    (CategoryTheory.MorphismProperty.coproducts.{u}
      (TopCat.realizedBoundaryInclusions ⊔ TopCat.realizedHornInclusions :
        CategoryTheory.MorphismProperty TopCat.{u})).pushouts ≤
      TopCat.closedT1Embeddings :=
  TopCat.pushouts_coproducts_realizedGenerators_le_closedT1Embeddings

theorem transfiniteCompositionsOfShape_pushouts_coproducts_generators_le_closedT1_client
    {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J]
    [WellFoundedLT J] :
    CategoryTheory.MorphismProperty.transfiniteCompositionsOfShape
      (CategoryTheory.MorphismProperty.coproducts.{u}
        (TopCat.realizedBoundaryInclusions ⊔ TopCat.realizedHornInclusions :
          CategoryTheory.MorphismProperty TopCat.{u})).pushouts J ≤
      TopCat.closedT1Embeddings :=
  TopCat.transfiniteCompositionsOfShape_pushouts_coproducts_generators_le_closedT1

theorem relativeCellComplex_mem_closedT1Embeddings_client
    {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J]
    [WellFoundedLT J]
    {α : J → Type*} {A B : (j : J) → α j → TopCat.{u}}
    {X Y : TopCat.{u}} {f : X ⟶ Y}
    (basicCell : (j : J) → (i : α j) → A j i ⟶ B j i)
    (c : HomotopicalAlgebra.RelativeCellComplex.{u} basicCell f)
    (hc : ∀ s : c.Cells, (TopCat.realizedBoundaryInclusions ⊔
      TopCat.realizedHornInclusions :
      CategoryTheory.MorphismProperty TopCat.{u}) (basicCell s.j s.i)) :
    TopCat.closedT1Embeddings f :=
  TopCat.relativeCellComplex_mem_closedT1Embeddings basicCell c hc

theorem relativeCellComplex_transfiniteCompositionOfShape_closedEmbeddings_of_small_client
    {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J]
    [WellFoundedLT J]
    (I : CategoryTheory.MorphismProperty TopCat.{u})
    (hI : I ≤ TopCat.closedEmbeddings)
    {X Y : TopCat.{u}} {f : X ⟶ Y}
    (c : HomotopicalAlgebra.RelativeCellComplex.{u_1}
      (fun (_ : J) ↦ I.homFamily) f)
    (hSmall : ∀ (j : J) (hj : ¬IsMax j),
      Small.{u} ((c.attachCells j hj).ι))
    {a b : J} (φ : a ⟶ b) :
    Topology.IsClosedEmbedding ((c.F.map φ).hom) :=
  (TopCat.closedEmbeddings_iff _).mp
    ((TopCat.relativeCellComplex_transfiniteCompositionOfShape_closedEmbeddings_of_small
      I hI c hSmall).mem_map φ)

#print axioms TopCat.realizedGenerators_le_closedEmbeddings
#print axioms TopCat.relativeCellComplex_mem_closedEmbeddings
#print axioms realizedGenerators_le_closedEmbeddings_client
#print axioms relativeCellComplex_mem_closedEmbeddings_client
#print axioms TopCat.relativeCellComplex_mem_closedT1Embeddings
#print axioms relativeCellComplex_mem_closedT1Embeddings_client

end TopCatRealizedCellClosedEmbeddingTests
end MathlibExtTest.AlgebraicTopology.ModelCategory
