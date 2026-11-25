/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeAfterMonomorphism
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeThroughPrism

/-!
# Focused clients of the coherent-cone weights

Concrete checks on the vertices `0, 1, 2` of `Vertex 2`.

* Marking: in the cone weight of `0`, the edge `{0, 2} ⊆ {0, 1, 2}` keeps the maximum `2` and is
  marked, while `{0, 1} ⊆ {0, 1, 2}` raises it and is not.
* The positive-maximum inclusion `coneAfterInclusion` is a monomorphism by `inferInstance`. Above
  the cutoff it is an isomorphism; at the cutoff it is not, since it misses the singleton `{0}`.
* Split: the cone `{0, 1, 2}` through `1` splits into the lower path `{0, 1}` and the upper cone
  `{1, 2}`, which keeps its maximum, and splitting round-trips both ways. For the pivot `0` the
  upper cone is the whole cone.
* Prism: the through-cone weight is a prism; its isomorphism round-trips a concrete vertex, and a
  through-cone edge is marked exactly when its upper-cone image is.
-/

set_option autoImplicit false

open CategoryTheory Opposite
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.MarkedCoherentConeClients

open SSet SSet.Marked SSet.Marked.CoherentWeight

/-- The vertex `k` of `Vertex 2`. -/
abbrev V (k : Fin 3) : Vertex.{u} 2 :=
  ⟨k⟩

/-! ### Concrete cone subsets of the vertex `0` -/

/-- The cone subset `{0}`. -/
def c0 : ConeSubset (V.{u} 0) where
  vertices := {V 0}
  mem := by decide
  lower := by decide

/-- The cone subset `{0, 1}`. -/
def c01 : ConeSubset (V.{u} 0) where
  vertices := {V 0, V 1}
  mem := by decide
  lower := by decide

/-- The cone subset `{0, 2}`. -/
def c02 : ConeSubset (V.{u} 0) where
  vertices := {V 0, V 2}
  mem := by decide
  lower := by decide

/-- The cone subset `{0, 1, 2}`. -/
def c012 : ConeSubset (V.{u} 0) where
  vertices := {V 0, V 1, V 2}
  mem := by decide
  lower := by decide

theorem c0_maximum : c0.{u}.maximum = V 0 := by
  decide

theorem c01_maximum : c01.{u}.maximum = V 1 := by
  decide

theorem c02_maximum : c02.{u}.maximum = V 2 := by
  decide

theorem c012_maximum : c012.{u}.maximum = V 2 := by
  decide

theorem c01_le : c01.{u} ≤ c012 := by
  change c01.vertices ⊆ c012.vertices
  decide

theorem c02_le : c02.{u} ≤ c012 := by
  change c02.vertices ⊆ c012.vertices
  decide

/-! ### Marking -/

/-- The edge `{0, 2} ⊆ {0, 1, 2}` keeps the maximum, so it is marked. -/
theorem edge_02_marked :
    (ComposableArrows.mk₁ (homOfLE c02_le) : (nerve (ConeSubset (V.{u} 0))) _⦋1⦌) ∈
      (coneWeight (V 0)).marking :=
  (coneWeight_marking _ _).mpr (c02_maximum.trans c012_maximum.symm)

/-- The edge `{0, 1} ⊆ {0, 1, 2}` raises the maximum, so it is not marked. -/
theorem edge_01_not_marked :
    (ComposableArrows.mk₁ (homOfLE c01_le) : (nerve (ConeSubset (V.{u} 0))) _⦋1⦌) ∉
      (coneWeight (V 0)).marking := fun h => by
  have h' : c01.{u}.maximum = c012.maximum := (coneWeight_marking _ _).mp h
  rw [c01_maximum, c012_maximum] at h'
  exact absurd h' (by decide)

/-! ### The positive-maximum inclusion -/

example : Mono (coneAfterInclusion (V.{u} 0) (V 0)) :=
  inferInstance

example : Mono (coneAfterInclusion (V.{u} 0) (V 1)) :=
  inferInstance

/-- Above the cutoff the inclusion is an isomorphism. -/
example : IsIso (coneAfterInclusion (V.{u} 1) (V 0)) := by
  rw [← coneAfterAboveIso_hom (show V.{u} 0 < V 1 by decide)]
  infer_instance

/-- At the cutoff it is not: no cone after `0` lies over the singleton `{0}`. -/
theorem not_isIso_at_cutoff : ¬ IsIso (coneAfterInclusion (V.{u} 0) (V 0)) := by
  intro h
  let v : (nerve (ConeSubset (V.{u} 0))) _⦋0⦌ := ComposableArrows.mk₀ c0
  let x := (inv (coneAfterInclusion (V.{u} 0) (V 0))).hom.app (op ⦋0⦌) v
  have hx : (coneAfterInclusion (V.{u} 0) (V 0)).hom.app (op ⦋0⦌) x = v :=
    congrArg (fun m : coneWeight (V.{u} 0) ⟶ coneWeight (V 0) => m.hom.app (op ⦋0⦌) v)
      (IsIso.inv_hom_id (coneAfterInclusion (V.{u} 0) (V 0)))
  have h0 : (x.obj 0).val = c0 :=
    congrArg (fun y : (nerve (ConeSubset (V.{u} 0))) _⦋0⦌ => y.obj 0) hx
  have hlt : V.{u} 0 < (x.obj 0).val.maximum := (x.obj 0).property
  rw [h0, c0_maximum] at hlt
  exact absurd hlt (by decide)

/-! ### Split -/

/-- The cone `{0, 1, 2}` through the pivot `1`. -/
def t012 : ConeThrough (V.{u} 0) (V 1) :=
  ⟨c012, by decide⟩

/-- The upper cone is `{1, 2}`. -/
theorem split_upper :
    V.{u} 1 ∈ (coneThroughSplitEquiv _ _ t012.{u}).2.vertices ∧
      V.{u} 2 ∈ (coneThroughSplitEquiv _ _ t012.{u}).2.vertices ∧
        V.{u} 0 ∉ (coneThroughSplitEquiv _ _ t012.{u}).2.vertices := by
  decide

/-- The lower path is `{0, 1}`. -/
theorem split_lower :
    V.{u} 0 ∈ (coneThroughSplitEquiv _ _ t012.{u}).1.I ∧
      V.{u} 1 ∈ (coneThroughSplitEquiv _ _ t012.{u}).1.I ∧
        V.{u} 2 ∉ (coneThroughSplitEquiv _ _ t012.{u}).1.I := by
  refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, fun h => absurd h.2 (by decide)⟩

/-- The upper cone keeps the maximum `2`. -/
example : (throughUpperCone t012.{u}).maximum = V 2 :=
  (throughUpperCone_maximum t012).trans c012_maximum

/-- Splitting round-trips. -/
example : (coneThroughSplitEquiv _ _).symm (coneThroughSplitEquiv _ _ t012.{u}) = t012 :=
  pathThrough_split t012

example : coneThroughSplitEquiv _ _ ((coneThroughSplitEquiv (V.{u} 0) (V 1)).symm
    (coneThroughSplitEquiv _ _ t012.{u})) = coneThroughSplitEquiv _ _ t012 :=
  (coneThroughSplitEquiv _ _).apply_symm_apply _

/-- Boundary case: for the pivot `0` the upper cone is the whole cone. -/
theorem split_pivot_zero (t : Vertex.{u} 2) :
    t ∈ (throughUpperCone (⟨c012, by decide⟩ : ConeThrough (V.{u} 0) (V 0))).vertices ↔
      t ∈ c012.vertices := by
  change t ∈ c012.vertices.filter (fun s => V 0 ≤ s) ↔ _
  rw [Finset.mem_filter]
  exact ⟨fun h => h.1, fun h => ⟨h, c012.lower t h⟩⟩

/-! ### Prism -/

/-- The vertex `{0, 1, 2}` of the through-cone weight. -/
abbrev v012 : (coneThroughWeight (V.{u} 0) (V 1)).toSSet _⦋0⦌ :=
  ComposableArrows.mk₀ t012

/-- The prism sends it to its upper cone ... -/
example : (((throughPrismIso (V.{u} 0) (V 1)).hom.hom.app (op ⦋0⦌) v012).2.obj 0) =
    throughUpperCone t012 :=
  rfl

/-- ... and back. -/
theorem prism_round_trip :
    (throughPrismIso (V.{u} 0) (V 1)).inv.hom.app (op ⦋0⦌)
      ((throughPrismIso (V.{u} 0) (V 1)).hom.hom.app (op ⦋0⦌) v012) = v012 :=
  congrArg (fun m : coneThroughWeight (V.{u} 0) (V 1) ⟶ coneThroughWeight (V 0) (V 1) =>
    m.hom.app (op ⦋0⦌) v012) (throughPrismIso (V.{u} 0) (V 1)).hom_inv_id

/-- For the pivot `0`, the edge `{0, 2} ⊆ {0, 1, 2}` of the through-cone. -/
abbrev throughEdge : (coneThroughWeight (V.{u} 0) (V 0)).toSSet _⦋1⦌ :=
  ComposableArrows.mk₁ (X₀ := (⟨c02, by decide⟩ : ConeThrough (V.{u} 0) (V 0)))
    (X₁ := ⟨c012, by decide⟩) (homOfLE c02_le)

/-- It is marked, and its prism image is marked too. -/
theorem throughEdge_marked : throughEdge.{u} ∈ (coneThroughWeight (V.{u} 0) (V 0)).marking :=
  (coneWeight_marking _ _).mpr (c02_maximum.trans c012_maximum.symm)

example : (throughPrismHom (V.{u} 0) (V 0)).app (op ⦋1⦌) throughEdge ∈
    (Marked.prod (Marked.max (nerve (SimplicialThickening.Path (V.{u} 0) (V 0))))
      (coneWeight (V 0))).marking :=
  (throughPrism_marking_iff _ _ _).mp throughEdge_marked

end MathlibExtTest.AlgebraicTopology.SimplicialSet.MarkedCoherentConeClients
