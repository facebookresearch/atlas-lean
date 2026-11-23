/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatGenerators
public import MathlibExt.Topology.Category.TopCat.Embedding.ClosedEmbeddingColimits
public import MathlibExt.Topology.Category.TopCat.Embedding.ClosedEmbeddingTransfinite
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.AlgebraicTopology.RelativeCellComplex.Basic
public import Mathlib.Logic.Small.Defs

/-!
# Realized-cell closed-embedding bridge in `TopCat`

This file is part of the KQ3 layer. It composes the accepted realized-generator
bounds with the accepted closed-embedding stability package: both
`TopCat.realizedBoundaryInclusions` and `TopCat.realizedHornInclusions` lie in
`TopCat.closedT1Embeddings`, hence in `TopCat.closedEmbeddings`, and the latter
is stable under coproducts, pushouts, and transfinite composition. The final
corollary turns any relative cell complex whose cells lie in the generator union
into a closed embedding via `RelativeCellComplex.transfiniteCompositionOfShape'`,
matching the shape needed by
`IsCardinalForSmallObjectArgument.preservesColimit`. No small-object,
factorization, model-structure, or weak-equivalence claim is made here.
A larger cell-index universe is covered under per-step `Small` via
`relativeCellComplex_transfiniteCompositionOfShape_closedEmbeddings_of_small`.
-/

@[expose] public section

universe u u_1

open CategoryTheory HomotopicalAlgebra MorphismProperty

namespace TopCat

/-- Realized boundary inclusions are closed embeddings. -/
theorem realizedBoundaryInclusions_le_closedEmbeddings :
    realizedBoundaryInclusions ≤ closedEmbeddings.{u} :=
  le_trans realizedBoundaryInclusions_le_closedT1Embeddings
    closedT1Embeddings_le_closedEmbeddings

/-- Realized horn inclusions are closed embeddings. -/
theorem realizedHornInclusions_le_closedEmbeddings :
    realizedHornInclusions ≤ closedEmbeddings.{u} :=
  le_trans realizedHornInclusions_le_closedT1Embeddings
    closedT1Embeddings_le_closedEmbeddings

/-- The generator union lies in closed embeddings. -/
theorem realizedGenerators_le_closedEmbeddings :
    (realizedBoundaryInclusions ⊔ realizedHornInclusions :
      MorphismProperty TopCat.{u}) ≤ closedEmbeddings :=
  sup_le realizedBoundaryInclusions_le_closedEmbeddings
    realizedHornInclusions_le_closedEmbeddings

/-- Pushouts of generator coproducts are closed embeddings. -/
theorem pushouts_coproducts_realizedGenerators_le_closedEmbeddings :
    (coproducts.{u} (realizedBoundaryInclusions ⊔ realizedHornInclusions :
      MorphismProperty TopCat.{u})).pushouts ≤ closedEmbeddings :=
  pushouts_le_iff.mpr (coproducts_le_iff.mpr realizedGenerators_le_closedEmbeddings)

variable {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J]
  [WellFoundedLT J]

/-- Transfinite compositions of generator pushouts are closed embeddings. -/
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

/-- Any relative cell complex built from the generators is a closed embedding. -/
theorem relativeCellComplex_mem_closedEmbeddings
    (c : RelativeCellComplex.{u} basicCell f)
    (hc : ∀ s : c.Cells, (realizedBoundaryInclusions ⊔ realizedHornInclusions :
      MorphismProperty TopCat.{u}) (basicCell s.j s.i)) :
    closedEmbeddings f :=
  transfiniteCompositionsOfShape_pushouts_coproducts_generators_le _
    ⟨c.transfiniteCompositionOfShape' hc⟩

/-- This definition exhibits the map as a transfinite composition of closed
    embeddings of shape `J`, using `Small.{u}` attachment indices to bridge
    the cell-index universe. Assumes `I ≤ closedEmbeddings`. This adds neither
    a closed-T1 result nor merely a final-membership wrapper. -/
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

/-- The generator union lies in closed T1-embeddings. -/
theorem realizedGenerators_le_closedT1Embeddings :
    (realizedBoundaryInclusions ⊔ realizedHornInclusions :
      MorphismProperty TopCat.{u}) ≤ closedT1Embeddings :=
  sup_le realizedBoundaryInclusions_le_closedT1Embeddings
    realizedHornInclusions_le_closedT1Embeddings

/-- Coproducts of generators are closed T1-embeddings. -/
theorem coproducts_realizedGenerators_le_closedT1Embeddings :
    coproducts.{u} (realizedBoundaryInclusions ⊔ realizedHornInclusions :
      MorphismProperty TopCat.{u}) ≤ closedT1Embeddings :=
  coproducts_le_iff.mpr realizedGenerators_le_closedT1Embeddings

/-- Pushouts of generator coproducts are closed T1-embeddings. -/
theorem pushouts_coproducts_realizedGenerators_le_closedT1Embeddings :
    (coproducts.{u} (realizedBoundaryInclusions ⊔ realizedHornInclusions :
      MorphismProperty TopCat.{u})).pushouts ≤ closedT1Embeddings :=
  pushouts_le_iff.mpr coproducts_realizedGenerators_le_closedT1Embeddings

/-- Transfinite compositions of generator pushouts are closed T1-embeddings. -/
theorem transfiniteCompositionsOfShape_pushouts_coproducts_generators_le_closedT1 :
    transfiniteCompositionsOfShape
      (coproducts.{u} (realizedBoundaryInclusions ⊔ realizedHornInclusions :
        MorphismProperty TopCat.{u})).pushouts J ≤ closedT1Embeddings := by
  calc _ ≤ transfiniteCompositionsOfShape closedT1Embeddings.{u} J :=
        transfiniteCompositionsOfShape_monotone J
          pushouts_coproducts_realizedGenerators_le_closedT1Embeddings
    _ ≤ closedT1Embeddings :=
        transfiniteCompositionsOfShape_le (W := closedT1Embeddings.{u}) (J := J)

/-- Any relative cell complex built from the generators is a closed T1-embedding. -/
theorem relativeCellComplex_mem_closedT1Embeddings
    (c : RelativeCellComplex.{u} basicCell f)
    (hc : ∀ s : c.Cells, (realizedBoundaryInclusions ⊔ realizedHornInclusions :
      MorphismProperty TopCat.{u}) (basicCell s.j s.i)) :
    closedT1Embeddings f :=
  transfiniteCompositionsOfShape_pushouts_coproducts_generators_le_closedT1 _
    ⟨c.transfiniteCompositionOfShape' hc⟩

end TopCat
