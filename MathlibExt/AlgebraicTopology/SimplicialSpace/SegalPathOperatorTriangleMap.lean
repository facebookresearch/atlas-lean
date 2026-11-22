/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalPathOperatorTriangle

/-!
# The original triangle map on every prescribed-tail path fibre

Restriction of the original shifted simplex to the actual operator
triangle retains the old and new leading edges and the given whole
tail simplex. The original tail edge supplies the second triangle edge,
with its same source and target vertices.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SimplicialSpace.LeftDecalageObject

/-- The actual original tail edge of the supplied whole simplex at the operator's initial edge. -/
def operatorTailEdge {m n : ℕ} (W : SimplicialSpace.{u})
    (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (b : (Δ[0] : SSet.{u}) ⟶ W.diagram _⦋n⦌) : (W.diagram _⦋1⦌) _⦋0⦌ :=
  SSet.yonedaEquiv (b ≫ W.diagram.map (operatorInitialEdge f).op)

/-- The actual original operator triangle in the prescribed whole tail fibre. -/
def rowPointTriangle {m n : ℕ} (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (b : (Δ[0] : SSet.{u}) ⟶ W.diagram _⦋n⦌) : rowPointFibre W x n b ⟶ W.diagram _⦋2⦌ :=
  pullback.fst _ _ ≫ (toDecalage W x).app (op (SimplexCategory.mk n)) ≫
    W.diagram.map (operatorTriangle f).op

set_option backward.isDefEq.respectTransparency false in
/-- The original triangle's first edge is exactly the original leading edge. -/
theorem rowPointTriangle_first {m n : ℕ} (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (b : (Δ[0] : SSet.{u}) ⟶ W.diagram _⦋n⦌) :
    rowPointTriangle W x f b ≫ W.diagram.δ (2 : Fin 3) = rowPointEdge W x n b := by
  unfold rowPointTriangle rowPointEdge
  simp only [Category.assoc, SimplicialObject.δ]
  rw [← W.diagram.map_comp, ← op_comp, operatorTriangle_first]

set_option backward.isDefEq.respectTransparency false in
/-- The original triangle's middle edge is exactly the new leading edge of the whole operator fibre map. -/
theorem rowPointTriangle_middle {m n : ℕ} (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (b : (Δ[0] : SSet.{u}) ⟶ W.diagram _⦋n⦌) :
    rowPointTriangle W x f b ≫ W.diagram.δ (1 : Fin 3) =
      rowPointOperator W x f b ≫ rowPointEdge W x m (b ≫ W.diagram.map f.op) := by
  unfold rowPointTriangle rowPointEdge
  simp only [Category.assoc]
  rw [← Category.assoc (rowPointOperator W x f b), rowPointOperator_fst]
  simp only [Category.assoc]
  have hn := (toDecalage W x).naturality f.op
  change rowOperator W x f ≫ (toDecalage W x).app (op (SimplexCategory.mk m)) =
    (toDecalage W x).app (op (SimplexCategory.mk n)) ≫
      W.diagram.map (SimplicialObject.LeftDecalage.ordinal.map f).op at hn
  rw [← Category.assoc (rowOperator W x f), hn]
  simp only [Category.assoc]
  simp only [SimplicialObject.δ]
  rw [← W.diagram.map_comp, ← W.diagram.map_comp, ← op_comp, ← op_comp, operatorTriangle_middle]

set_option backward.isDefEq.respectTransparency false in
/-- The original triangle's last edge is the actual tail edge of the same prescribed full simplex. -/
theorem rowPointTriangle_last {m n : ℕ} (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (b : (Δ[0] : SSet.{u}) ⟶ W.diagram _⦋n⦌) :
    rowPointTriangle W x f b ≫ W.diagram.δ (0 : Fin 3) =
      pullback.snd _ _ ≫ SSet.yonedaEquiv.symm (operatorTailEdge W f b) := by
  unfold rowPointTriangle
  simp only [Category.assoc, SimplicialObject.δ]
  rw [← W.diagram.map_comp, ← op_comp, operatorTriangle_last, op_comp, W.diagram.map_comp]
  change (pullback.fst _ _ ≫ (projection W x).app (op (SimplexCategory.mk n))) ≫
    W.diagram.map (operatorInitialEdge f).op = _
  rw [pullback.condition]
  simp only [Category.assoc, operatorTailEdge, Equiv.symm_apply_apply]

end SimplicialSpace.LeftDecalageObject
