/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalPathLeadingEdgeComparison
import MathlibExt.AlgebraicTopology.SimplicialSpace.LeftDecalageObjectRowFibration

/-!
# The actual point fibres of original fixed-object Segal path rows

Fix the entire original tail simplex. The actual fibre comparison keeps
that whole tail and its original leading edge. Its target is the
original mapping fibre from the prescribed source object to the actual
first vertex of that same tail simplex.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SimplicialSpace.LeftDecalageObject

/-- The actual whole fibre of the original path projection over the prescribed entire tail simplex. -/
abbrev rowPointFibre (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) (n : ℕ)
    (b : (Δ[0] : SSet.{u}) ⟶ W.diagram _⦋n⦌) : SSet.{u} :=
  pullback ((projection W x).app (op (SimplexCategory.mk n))) b

/-- The first original vertex of the supplied entire tail simplex. -/
def tailFirstPoint (W : SimplicialSpace.{u}) (n : ℕ) (b : (Δ[0] : SSet.{u}) ⟶ W.diagram _⦋n⦌) :
    (W.diagram _⦋0⦌) _⦋0⦌ :=
  SSet.yonedaEquiv (b ≫ InitialEdgeTailMapping.tailFirstVertex W n)

/-- The actual original leading edge of the full point fibre. -/
def rowPointEdge (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) (n : ℕ)
    (b : (Δ[0] : SSet.{u}) ⟶ W.diagram _⦋n⦌) : rowPointFibre W x n b ⟶ W.diagram _⦋1⦌ :=
  pullback.fst _ _ ≫ (toDecalage W x).app (op (SimplexCategory.mk n)) ≫
    W.diagram.map (SimplexCategory.mkOfSucc (0 : Fin (n + 1))).op

set_option backward.isDefEq.respectTransparency false in
/-- The whole original point-fibre leading edge retains its same prescribed source object. -/
theorem rowPointEdge_source (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) (n : ℕ)
    (b : (Δ[0] : SSet.{u}) ⟶ W.diagram _⦋n⦌) :
    rowPointEdge W x n b ≫ W.diagram.δ (1 : Fin 2) =
      pullback.snd _ _ ≫ SSet.yonedaEquiv.symm x := by
  unfold rowPointEdge
  simp only [Category.assoc]
  have he : W.diagram.map (SimplexCategory.mkOfSucc (0 : Fin (n + 1))).op ≫
      W.diagram.δ (1 : Fin 2) =
    (SimplicialObject.LeftDecalage.augmentation W.diagram).app (op (SimplexCategory.mk n)) := by
    change W.diagram.map _ ≫ W.diagram.map _ = W.diagram.map _
    rw [← W.diagram.map_comp, ← op_comp]
    apply congrArg W.diagram.map
    apply Quiver.Hom.unop_inj
    ext i
    fin_cases i
    rfl
  rw [he]
  have hc := congrArg (fun q : diagram W x ⟶
      (SimplicialObject.const SSet.{u}).obj (W.diagram _⦋0⦌) => q.app (op (SimplexCategory.mk n)))
    (fixedObject W x)
  change (toDecalage W x).app (op (SimplexCategory.mk n)) ≫
      (SimplicialObject.LeftDecalage.augmentation W.diagram).app (op (SimplexCategory.mk n)) =
    (toPoint W x).app (op (SimplexCategory.mk n)) ≫ SSet.yonedaEquiv.symm x at hc
  rw [hc]
  have hp : pullback.fst ((projection W x).app (op (SimplexCategory.mk n))) b ≫
      (toPoint W x).app (op (SimplexCategory.mk n)) = pullback.snd _ _ :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  exact (Category.assoc _ _ _).symm.trans (congrArg (fun q => q ≫ SSet.yonedaEquiv.symm x) hp)

set_option backward.isDefEq.respectTransparency false in
/-- The whole original point-fibre leading edge retains the actual first vertex of its prescribed full tail. -/
theorem rowPointEdge_target (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) (n : ℕ)
    (b : (Δ[0] : SSet.{u}) ⟶ W.diagram _⦋n⦌) :
    rowPointEdge W x n b ≫ W.diagram.δ (0 : Fin 2) =
      pullback.snd _ _ ≫ SSet.yonedaEquiv.symm (tailFirstPoint W n b) := by
  unfold rowPointEdge
  simp only [Category.assoc]
  have he : W.diagram.map (SimplexCategory.mkOfSucc (0 : Fin (n + 1))).op ≫
      W.diagram.δ (0 : Fin 2) =
    W.diagram.map (SimplexCategory.δ (0 : Fin (n + 2))).op ≫
      InitialEdgeTailMapping.tailFirstVertex W n := by
    change W.diagram.map _ ≫ W.diagram.map _ = W.diagram.map _ ≫ W.diagram.map _
    rw [← W.diagram.map_comp, ← W.diagram.map_comp, ← op_comp, ← op_comp]
    apply congrArg W.diagram.map
    apply Quiver.Hom.unop_inj
    ext i
    fin_cases i
    rfl
  rw [he, ← Category.assoc]
  change (pullback.fst _ _ ≫ (projection W x).app (op (SimplexCategory.mk n))) ≫ _ = _
  rw [pullback.condition]
  simp only [Category.assoc, tailFirstPoint, Equiv.symm_apply_apply]

/-- The entire original row-point leading edge maps to its same original mapping fibre. -/
def rowPointMappingComparison (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) (n : ℕ)
    (b : (Δ[0] : SSet.{u}) ⟶ W.diagram _⦋n⦌) :
    rowPointFibre W x n b ⟶ mappingFibre W x (tailFirstPoint W n b) :=
  pullback.lift (rowPointEdge W x n b) (pullback.snd _ _) (by
    apply prod.hom_ext
    · simpa only [Category.assoc, mappingEndpoint_fst, mappingPointPair_fst] using rowPointEdge_source W x n b
    · simpa only [Category.assoc, mappingEndpoint_snd, mappingPointPair_snd] using rowPointEdge_target W x n b)

/-- The whole original row-point mapping comparison retains its same actual point projection. -/
theorem rowPointMappingComparison_snd (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) (n : ℕ) (b : (Δ[0] : SSet.{u}) ⟶ W.diagram _⦋n⦌) :
    rowPointMappingComparison W x n b ≫ mappingFibre.snd W x (tailFirstPoint W n b) = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

end SimplicialSpace.LeftDecalageObject
