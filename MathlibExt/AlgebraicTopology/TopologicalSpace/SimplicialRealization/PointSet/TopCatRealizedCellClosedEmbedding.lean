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
public import MathlibExt.Topology.Category.TopCat.Embedding.ClosedEmbeddingColimits
public import MathlibExt.Topology.Category.TopCat.Embedding.ClosedEmbeddingTransfinite
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.AlgebraicTopology.RelativeCellComplex.Basic
public import Mathlib.Logic.Small.Defs

/-!
# Closed embeddings from realized-cell attachments

Realized simplicial boundary and horn inclusions are closed T1-embeddings: they are closed
embeddings and points outside the image have closed singletons. This property is stable under
coproducts, pushouts and transfinite compositions along a bottomed well-founded linear successor
order.

Consequently a relative cell complex whose attached cells belong to the realized-generator union
is a closed embedding, and in fact a closed T1-embedding. A separate construction for any family
of closed embeddings exhibits the transfinite-composition witness when each successor attachment
index type is Small relative to the space universe.

Space and shape parameters use universe u; the latter construction permits an independent
cell-index universe u₁, with the stated per-attachment smallness condition.
-/

@[expose] public section

universe u u_1

open CategoryTheory HomotopicalAlgebra MorphismProperty

namespace TopCat

/-- In TopCat of any universe u, every realized simplicial boundary inclusion is a closed embedding. -/
theorem realizedBoundaryInclusions_le_closedEmbeddings :
    realizedBoundaryInclusions ≤ closedEmbeddings.{u} :=
  le_trans realizedBoundaryInclusions_le_closedT1Embeddings
    closedT1Embeddings_le_closedEmbeddings

/-- In TopCat of any universe u, every realized simplicial horn inclusion is a closed embedding. -/
theorem realizedHornInclusions_le_closedEmbeddings :
    realizedHornInclusions ≤ closedEmbeddings.{u} :=
  le_trans realizedHornInclusions_le_closedT1Embeddings
    closedT1Embeddings_le_closedEmbeddings

/-- In TopCat of universe u, let G be the union of realized simplicial boundary and horn inclusions.
Every member of G is a closed embedding. -/
theorem realizedGenerators_le_closedEmbeddings :
    (realizedBoundaryInclusions ⊔ realizedHornInclusions :
      MorphismProperty TopCat.{u}) ≤ closedEmbeddings :=
  sup_le realizedBoundaryInclusions_le_closedEmbeddings
    realizedHornInclusions_le_closedEmbeddings

/-- In TopCat of universe u, let G be the union of realized simplicial boundary and horn inclusions.
Every pushout of a coproduct of G-maps is a closed embedding. -/
theorem pushouts_coproducts_realizedGenerators_le_closedEmbeddings :
    (coproducts.{u} (realizedBoundaryInclusions ⊔ realizedHornInclusions :
      MorphismProperty TopCat.{u})).pushouts ≤ closedEmbeddings :=
  pushouts_le_iff.mpr (coproducts_le_iff.mpr realizedGenerators_le_closedEmbeddings)

variable {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J]
  [WellFoundedLT J]

/-- In TopCat of universe u, let G be the union of realized simplicial boundary and horn inclusions.
Let J:Type u be a bottomed, well-founded linear order with a successor order. A transfinite
composition of shape J whose successor maps are pushouts of coproducts of G-maps is a closed
embedding. -/
theorem transfiniteCompositionsOfShape_pushouts_coproducts_generators_le :
    transfiniteCompositionsOfShape
      (coproducts.{u} (realizedBoundaryInclusions ⊔ realizedHornInclusions :
        MorphismProperty TopCat.{u})).pushouts J ≤ closedEmbeddings := by
  calc _ ≤ transfiniteCompositionsOfShape closedEmbeddings.{u} J :=
        transfiniteCompositionsOfShape_monotone J
          pushouts_coproducts_realizedGenerators_le_closedEmbeddings
    _ ≤ closedEmbeddings :=
        transfiniteCompositionsOfShape_le (W := closedEmbeddings.{u}) (J := J)

variable {α : J → Type*} {A B : (j : J) → α j → TopCat.{u}}
  {X Y : TopCat.{u}} {f : X ⟶ Y}
  (basicCell : (j : J) → (i : α j) → A j i ⟶ B j i)

/-- In TopCat of universe u, let G be the union of realized simplicial boundary and horn inclusions.
For a bottomed well-founded linear successor order J:Type u, a relative cell complex whose
actually attached cells belong to G has a closed-embedding structure on its total map. -/
theorem relativeCellComplex_mem_closedEmbeddings
    (c : RelativeCellComplex.{u} basicCell f)
    (hc : ∀ s : c.Cells, (realizedBoundaryInclusions ⊔ realizedHornInclusions :
      MorphismProperty TopCat.{u}) (basicCell s.j s.i)) :
    closedEmbeddings f :=
  transfiniteCompositionsOfShape_pushouts_coproducts_generators_le _
    ⟨c.transfiniteCompositionOfShape' hc⟩

/-- Let J be a bottomed, well-founded linear successor order in universe u and I a family of closed
embeddings in TopCat.{u}. For a relative I-cell complex with independent cell-index universe u₁,
assume every nonmaximal attachment index type is Small relative to u. Its total map is exhibited
as a transfinite composition of closed embeddings of shape J. -/
def relativeCellComplex_transfiniteCompositionOfShape_closedEmbeddings_of_small
    (I : MorphismProperty TopCat.{u})
    (hI : I ≤ closedEmbeddings)
    {X Y : TopCat.{u}} {f : X ⟶ Y}
    (c : RelativeCellComplex.{u_1} (fun (_ : J) ↦ I.homFamily) f)
    (hSmall : ∀ (j : J) (hj : ¬IsMax j),
      Small.{u} ((c.attachCells j hj).ι)) :
    closedEmbeddings.TransfiniteCompositionOfShape J f := by
  have hStep : ∀ (j : J) (hj : ¬IsMax j),
      (MorphismProperty.coproducts.{u} I).pushouts
        (c.F.map (homOfLE (Order.le_succ j))) := by
    intro j hj
    have := hSmall j hj
    let a' := (c.attachCells j hj).reindex (equivShrink _).symm
    have h := a'.pushouts_coproducts
    simpa using h
  have hCoproducts : MorphismProperty.coproducts.{u} I ≤ closedEmbeddings :=
    MorphismProperty.coproducts_le_iff.mpr hI
  have hPushouts : (MorphismProperty.coproducts.{u} I).pushouts ≤
      closedEmbeddings :=
    MorphismProperty.pushouts_le_iff.mpr hCoproducts
  exact {
    toTransfiniteCompositionOfShape := c.toTransfiniteCompositionOfShape
    map_mem := fun j hj => hPushouts _ (hStep j hj) }

/-- In TopCat of universe u, let G be the union of realized simplicial boundary and horn inclusions.
A closed T1-embedding is a closed embedding whose codomain singletons outside its image are
closed. Every member of G has this property. -/
theorem realizedGenerators_le_closedT1Embeddings :
    (realizedBoundaryInclusions ⊔ realizedHornInclusions :
      MorphismProperty TopCat.{u}) ≤ closedT1Embeddings :=
  sup_le realizedBoundaryInclusions_le_closedT1Embeddings
    realizedHornInclusions_le_closedT1Embeddings

/-- In TopCat of universe u, let G be the union of realized simplicial boundary and horn inclusions.
A closed T1-embedding is a closed embedding whose codomain singletons outside its image are
closed. Every coproduct of G-maps is a closed T1-embedding. -/
theorem coproducts_realizedGenerators_le_closedT1Embeddings :
    coproducts.{u} (realizedBoundaryInclusions ⊔ realizedHornInclusions :
      MorphismProperty TopCat.{u}) ≤ closedT1Embeddings :=
  coproducts_le_iff.mpr realizedGenerators_le_closedT1Embeddings

/-- In TopCat of universe u, let G be the union of realized simplicial boundary and horn inclusions.
A closed T1-embedding is a closed embedding whose codomain singletons outside its image are
closed. Every pushout of a coproduct of G-maps is a closed T1-embedding. -/
theorem pushouts_coproducts_realizedGenerators_le_closedT1Embeddings :
    (coproducts.{u} (realizedBoundaryInclusions ⊔ realizedHornInclusions :
      MorphismProperty TopCat.{u})).pushouts ≤ closedT1Embeddings :=
  pushouts_le_iff.mpr coproducts_realizedGenerators_le_closedT1Embeddings

/-- In TopCat of universe u, let G be the union of realized simplicial boundary and horn inclusions.
Let J:Type u be a bottomed, well-founded linear order with a successor order. A closed
T1-embedding is a closed embedding whose codomain singletons outside its image are closed.
Transfinite compositions of generator-coproduct pushouts retain this property. -/
theorem transfiniteCompositionsOfShape_pushouts_coproducts_generators_le_closedT1 :
    transfiniteCompositionsOfShape
      (coproducts.{u} (realizedBoundaryInclusions ⊔ realizedHornInclusions :
        MorphismProperty TopCat.{u})).pushouts J ≤ closedT1Embeddings := by
  calc _ ≤ transfiniteCompositionsOfShape closedT1Embeddings.{u} J :=
        transfiniteCompositionsOfShape_monotone J
          pushouts_coproducts_realizedGenerators_le_closedT1Embeddings
    _ ≤ closedT1Embeddings :=
        transfiniteCompositionsOfShape_le (W := closedT1Embeddings.{u}) (J := J)

/-- In TopCat of universe u, let G be the union of realized simplicial boundary and horn inclusions.
A closed T1-embedding is a closed embedding whose codomain singletons outside its image are
closed. For a bottomed well-founded linear successor order J:Type u, a relative cell complex
whose actually attached cells belong to G is a closed T1-embedding. -/
theorem relativeCellComplex_mem_closedT1Embeddings
    (c : RelativeCellComplex.{u} basicCell f)
    (hc : ∀ s : c.Cells, (realizedBoundaryInclusions ⊔ realizedHornInclusions :
      MorphismProperty TopCat.{u}) (basicCell s.j s.i)) :
    closedT1Embeddings f :=
  transfiniteCompositionsOfShape_pushouts_coproducts_generators_le_closedT1 _
    ⟨c.transfiniteCompositionOfShape' hc⟩

end TopCat
