/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatWeakHomotopyEquivalence
public import MathlibExt.Topology.Category.TopCat.Embedding.ClosedT1Embedding
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexW
public import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
public import MathlibExt.Topology.Category.TopCat.Colimits.TopCatSingularClosedTransfiniteContinuous

/-!
# Transfinite composition of closed-T1 weak homotopy equivalences

Let `J : Type v` be linearly ordered with a least element, a successor order, and well-founded
strict order. Let a map of `TopCat.{u}` be a `J`-shaped transfinite composite whose steps lie
in both `weakHomotopyEquivalences` and `closedT1Embeddings`. If the simplicial class
`SSet.KanComplex.W` is stable under transfinite composition of shape `J`, the topological
composite is a weak homotopy equivalence.

See Goerss–Jardine, *Simplicial Homotopy Theory*, I.3, for weak-equivalence and homotopy-group
conventions.
-/

@[expose] public section

open CategoryTheory Limits

universe v u

namespace TopCat

/-- Let `J : Type v` have `LinearOrder`, `OrderBot`, `SuccOrder`, and `WellFoundedLT`. Let `f:X→Y`
in `TopCat.{u}` have a `J`-shaped transfinite-composition witness for steps in
`weakHomotopyEquivalences ⊓ closedT1Embeddings`. Assume `(SSet.KanComplex.W : MorphismProperty
SSet.{u})` is stable under transfinite composition of shape `J`. Then
`weakHomotopyEquivalences f`. -/
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
