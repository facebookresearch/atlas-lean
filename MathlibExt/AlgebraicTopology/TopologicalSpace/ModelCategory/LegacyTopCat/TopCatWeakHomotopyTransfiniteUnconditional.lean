/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexWTransfinite
public import MathlibExt.Topology.Homotopy.TopCat.Singular.SingularKanPolymorphic
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatWeakHomotopyTransfiniteClosed

/-!
# Unconditional closed-T1 transfinite weak-equivalence closure

The singular functor preserves the actual colimit and well-order continuity
of a closed-T1 diagram. Its bottom stage is Kan. Per-diagram Kan-bottom
closure therefore proves that the included endpoint is a weak homotopy
equivalence for every shape whose universe is no larger than the universe of
the spaces.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory Limits

namespace TopCat

/-- A transfinite composition of closed-T1 weak homotopy equivalences is a
weak homotopy equivalence when the shape universe is no larger than the
universe of the spaces. -/
theorem weakHomotopyEquivalences.of_transfiniteComposition_closedT1_unconditional
    {J : Type v} [LinearOrder J] [OrderBot J] [SuccOrder J]
    [WellFoundedLT J] [UnivLE.{v, u}]
    {X Y : TopCat.{u}} {f : X ⟶ Y}
    (hf : (weakHomotopyEquivalences ⊓ closedT1Embeddings).TransfiniteCompositionOfShape
      J f) :
    weakHomotopyEquivalences f := by
  have hFclosed : ∀ ⦃i j : J⦄ (g : i ⟶ j),
      closedT1Embeddings (hf.F.map g) := by
    intro i j g
    simpa [MorphismProperty.TransfiniteCompositionOfShape.ofLE] using
      (hf.ofLE inf_le_right).mem_map g
  let _ : PreservesColimit hf.F TopCat.toSSet :=
    TopCat.preservesColimit_toSSet_of_closedT1_transfinite hFclosed
  let _ : hf.F.IsWellOrderContinuous :=
    hf.toTransfiniteCompositionOfShape.isWellOrderContinuous
  have hCont : (hf.F ⋙ TopCat.toSSet.{u}).IsWellOrderContinuous :=
    TopCat.isWellOrderContinuous_comp_toSSet_of_closedT1_transfinite hFclosed
  let hmap :
      (SSet.KanComplex.W : MorphismProperty SSet.{u}).TransfiniteCompositionOfShape
        J (TopCat.toSSet.map f) :=
    { F := hf.F ⋙ TopCat.toSSet.{u}
      isoBot := TopCat.toSSet.mapIso hf.isoBot
      isWellOrderContinuous := hCont
      incl := Functor.whiskerRight hf.incl TopCat.toSSet.{u} ≫
        (Functor.constComp _ _ _).hom
      isColimit := IsColimit.ofIsoColimit
        (isColimitOfPreserves TopCat.toSSet.{u} hf.isColimit)
        (Cocone.ext (Iso.refl _))
      fac := by simp [← Functor.map_comp]
      map_mem := fun j hj => (hf.ofLE inf_le_left).map_mem j hj }
  let _ : SSet.KanComplex (hmap.F.obj ⊥) :=
    TopCat.toSSet_obj_kanComplex (hf.F.obj ⊥)
  exact SSet.KanComplex.W.of_transfiniteCompositionOfShape_of_kan_bot hmap

end TopCat
