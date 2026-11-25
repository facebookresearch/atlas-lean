/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatWeakHomotopyEquivalence
public import MathlibExt.Topology.Category.TopCat.Embedding.ClosedT1Embedding
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexW
public import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
public import MathlibExt.Topology.Category.TopCat.Colimits.TopCatSingularClosedTransfiniteContinuous

/-!
# Transfinite closed-T1 stability for weak homotopy equivalences

Universe-polymorphic KQ3 packet. A transfinite composite of shape `J`
whose steps are both TopCat weak homotopy equivalences and closed-T1
embeddings is again a weak homotopy equivalence, assuming only
`SSet.KanComplex.W` stability under transfinite composition of shape `J`. Both mapped
preservation and well-order continuity for the witness diagram are
derived per-diagram from the closed-T1 steps; no global `TopCat.toSSet`
preservation is assumed.

The proof builds the mapped `W` witness directly on the original diagram
and closes with
`MorphismProperty.transfiniteCompositionsOfShape_le`. The
`closedT1Embeddings` half records the KQ3 cell-complex hypothesis fed by
`TopCat.relativeCellComplex_mem_closedT1Embeddings`; no closed-T1 fact is
reproved here.

This adds no unconditional closure, no plain-closed variant, no coproduct
or pushout closure, no model structure, and no KQ4 statement.

Mathematical source: Goerss--Jardine, Simplicial Homotopy Theory, I.3,
plus the Mathlib transfinite-composition API.
-/

@[expose] public section

open CategoryTheory Limits

universe v u

namespace TopCat

/-- Transfinite composite of closed-T1 weak homotopy equivalences is a
weak homotopy equivalence, assuming only `SSet.KanComplex.W` stability
under the shape. Both mapped preservation and well-order continuity for
the witness diagram are derived from the closed-T1 steps; no global
preservation is assumed. Directly consumes
`relativeCellComplex_mem_closedT1Embeddings`. -/
theorem weakHomotopyEquivalences.of_transfiniteComposition_closedT1
    {J : Type v} [LinearOrder J] [OrderBot J] [SuccOrder J]
    [WellFoundedLT J] {X Y : TopCat.{u}} {f : X ⟶ Y}
    (hf : (weakHomotopyEquivalences ⊓
      closedT1Embeddings).TransfiniteCompositionOfShape J f)
    [(SSet.KanComplex.W :
      MorphismProperty SSet.{u}).IsStableUnderTransfiniteCompositionOfShape
      J] :
    weakHomotopyEquivalences f := by
  -- Build the mapped `W` witness directly on `hf.F`, so the derived per-diagram
  -- instance applies definitionally; an opaque `have hW := hf.ofLE _`
  -- would leave `hW.F` unrelated to `hf.F`.
  have hFclosed : ∀ ⦃i j : J⦄ (g : i ⟶ j),
      closedT1Embeddings (hf.F.map g) := by
    intro i j g
    simpa [MorphismProperty.TransfiniteCompositionOfShape.ofLE] using
      (hf.ofLE inf_le_right).mem_map g
  have : PreservesColimit hf.F TopCat.toSSet :=
    TopCat.preservesColimit_toSSet_of_closedT1_transfinite hFclosed
  have : hf.F.IsWellOrderContinuous :=
    hf.toTransfiniteCompositionOfShape.isWellOrderContinuous
  have hCont : (hf.F ⋙ TopCat.toSSet.{u}).IsWellOrderContinuous :=
    TopCat.isWellOrderContinuous_comp_toSSet_of_closedT1_transfinite hFclosed
  have hmap :
      (SSet.KanComplex.W :
        MorphismProperty SSet.{u}).TransfiniteCompositionOfShape J
        (TopCat.toSSet.map f) := {
    F := hf.F ⋙ TopCat.toSSet.{u}
    isoBot := TopCat.toSSet.mapIso hf.isoBot
    isWellOrderContinuous := hCont
    incl :=
      Functor.whiskerRight hf.incl TopCat.toSSet.{u} ≫
        (Functor.constComp _ _ _).hom
    isColimit :=
      IsColimit.ofIsoColimit
        (isColimitOfPreserves TopCat.toSSet.{u} hf.isColimit)
        (Cocone.ext (Iso.refl _))
    fac := by simp [← Functor.map_comp]
    map_mem := fun j hj => (hf.ofLE inf_le_left).map_mem j hj
  }
  have hmem :
      (SSet.KanComplex.W :
        MorphismProperty SSet.{u}).transfiniteCompositionsOfShape J
        (TopCat.toSSet.map f) :=
    ⟨hmap⟩
  have hle :
      (SSet.KanComplex.W :
        MorphismProperty SSet.{u}).transfiniteCompositionsOfShape J ≤
        SSet.KanComplex.W :=
    MorphismProperty.transfiniteCompositionsOfShape_le
      (W := SSet.KanComplex.W) (J := J)
  exact hle _ hmem

end TopCat
