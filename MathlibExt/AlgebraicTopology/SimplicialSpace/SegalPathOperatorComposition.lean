/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalPathOperatorEdge
import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalMappingOperatorEquivalences

/-!
# The actual Segal path operator is composition by its original initial edge

The whole operator triangle retains the old and new leading edges and
the original edge of the prescribed tail. Its map into the existing
triangle-space pullback gives the original composition homotopy, which
is the genuine bridge for proving grouplike operator-fibre weakness.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped Simplicial

namespace SimplicialSpace.LeftDecalageObject

open SimplicialSpace.SegalHomotopy

private def homotopyPre {A B C : SSet.{u}} {f g : B ⟶ C} (H : SSet.Homotopy f g) (k : A ⟶ B) :
    SSet.Homotopy (k ≫ f) (k ≫ g) :=
  (show SSet.HomotopyRel (k ≫ f) (k ≫ g) (⊥ : A.Subcomplex) from
    { h := (k ▷ (Δ[1] : SSet.{u})) ≫ H.h
      h₀ := by rw [← Category.assoc, SSet.ι₀_comp, Category.assoc, H.h₀]
      h₁ := by rw [← Category.assoc, SSet.ι₁_comp, Category.assoc, H.h₁]
      stationary := by intro n a ha t; cases ha }).toHomotopy

/-- The original pair of short edges in the whole operator triangle. -/
def operatorShortEdges {m n : ℕ} (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (b : (Δ[0] : SSet.{u}) ⟶ W.diagram _⦋n⦌) :
    rowPointFibre W x n b ⟶ mappingFibre W x (tailFirstPoint W n b) ⨯
      mappingFibre W (tailFirstPoint W n b) (tailFirstPoint W m (b ≫ W.diagram.map f.op)) :=
  prod.lift (rowPointMappingComparison W x n b) (pullback.snd _ _ ≫ operatorEdgeFibreMap W f b)

set_option backward.isDefEq.respectTransparency false in
/-- The entire original operator triangle maps to the actual prescribed-endpoint triangle space. -/
def operatorTriangleSpaceMap {m n : ℕ} (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (b : (Δ[0] : SSet.{u}) ⟶ W.diagram _⦋n⦌) :
    rowPointFibre W x n b ⟶ triangleSpace W x (tailFirstPoint W n b)
      (tailFirstPoint W m (b ≫ W.diagram.map f.op)) :=
  pullback.lift (rowPointTriangle W x f b) (operatorShortEdges W x f b) (by
    apply pullback.hom_ext
    · simp only [Category.assoc, twoEdgeComparison_fst, twoEdgePair_fst]
      rw [operatorShortEdges, ← Category.assoc, prod.lift_fst, rowPointMappingComparison, pullback.lift_fst]
      exact rowPointTriangle_first W x f b
    · simp only [Category.assoc, twoEdgeComparison_snd, twoEdgePair_snd]
      rw [operatorShortEdges, ← Category.assoc, prod.lift_snd, Category.assoc,
        operatorEdgeFibreMap, pullback.lift_fst]
      simpa only [operatorTailEdge, operatorEdgeMap, Equiv.symm_apply_apply] using
        rowPointTriangle_last W x f b)

/-- The whole original operator triangle has its exact prescribed pair of original short edges. -/
theorem operatorTriangleSpaceMap_pair {m n : ℕ} (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (b : (Δ[0] : SSet.{u}) ⟶ W.diagram _⦋n⦌) :
    operatorTriangleSpaceMap W x f b ≫
        triangleComparison W x (tailFirstPoint W n b) (tailFirstPoint W m (b ≫ W.diagram.map f.op)) =
      operatorShortEdges W x f b := pullback.lift_snd _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- The original operator triangle's middle mapping fibre is exactly the actual whole path-row transition. -/
theorem operatorTriangleSpaceMap_middle {m n : ℕ} (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (b : (Δ[0] : SSet.{u}) ⟶ W.diagram _⦋n⦌) :
    operatorTriangleSpaceMap W x f b ≫
        triangleMiddle W x (tailFirstPoint W n b) (tailFirstPoint W m (b ≫ W.diagram.map f.op)) =
      rowPointOperator W x f b ≫ rowPointMappingComparison W x m (b ≫ W.diagram.map f.op) := by
  apply pullback.hom_ext
  · rw [Category.assoc, triangleMiddle_fst, ← Category.assoc, operatorTriangleSpaceMap,
      pullback.lift_fst, rowPointTriangle_middle, Category.assoc]
    exact congrArg (fun q => rowPointOperator W x f b ≫ q) (pullback.lift_fst _ _ _).symm
  · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

/-- The actual original operator triangle supplies the genuine whole composition homotopy. -/
def operatorCompositionHomotopy {m n : ℕ} (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x : (W.diagram _⦋0⦌) _⦋0⦌) (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (b : (Δ[0] : SSet.{u}) ⟶ W.diagram _⦋n⦌) :
    SSet.Homotopy
      (operatorTriangleSpaceMap W x f b ≫
        triangleMiddle W x (tailFirstPoint W n b) (tailFirstPoint W m (b ≫ W.diagram.map f.op)))
      (operatorShortEdges W x f b ≫ mappingComposition W hW x (tailFirstPoint W n b)
        (tailFirstPoint W m (b ≫ W.diagram.map f.op))) := by
  have H := homotopyPre (mappingCompositionOfTriangle W hW x (tailFirstPoint W n b)
    (tailFirstPoint W m (b ≫ W.diagram.map f.op))) (operatorTriangleSpaceMap W x f b)
  simpa only [← Category.assoc, operatorTriangleSpaceMap_pair] using H

set_option backward.isDefEq.respectTransparency false in
/-- The actual original path-row transition is homotopic to composing its old leading edge with the original operator edge. -/
def rowPointOperatorCompositionHomotopy {m n : ℕ} (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x : (W.diagram _⦋0⦌) _⦋0⦌) (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (b : (Δ[0] : SSet.{u}) ⟶ W.diagram _⦋n⦌) :
    SSet.Homotopy
      (rowPointOperator W x f b ≫ rowPointMappingComparison W x m (b ≫ W.diagram.map f.op))
      (operatorShortEdges W x f b ≫ mappingComposition W hW x (tailFirstPoint W n b)
        (tailFirstPoint W m (b ≫ W.diagram.map f.op))) := by
  simpa only [operatorTriangleSpaceMap_middle] using operatorCompositionHomotopy W hW x f b

end SimplicialSpace.LeftDecalageObject
