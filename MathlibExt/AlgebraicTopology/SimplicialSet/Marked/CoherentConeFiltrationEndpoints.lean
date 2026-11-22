/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeCellSquare

/-!
# Original empty stages and the actual new-vertex free cell

The preceding stage is empty at and beyond the selected new vertex.
The bounded stage at that vertex consists of its actual singleton.
The free upper-cell map there is a strict isomorphism with its native
point and path coordinates; beyond that vertex both original values
are empty. No replacement or weak-equivalence outcome is used.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- The original strict stage has no subsets at or beyond the new least vertex. -/
theorem coneBefore_isEmpty {n : ℕ} {i k : Vertex.{u} n} (h : k ≤ i) : IsEmpty (ConeBefore i k) :=
  ⟨fun a => (not_lt_of_ge h) (coneBefore_least_lt a)⟩

/-- The original bounded stage has no subsets strictly beyond its selected maximum. -/
theorem coneAtMost_isEmpty {n : ℕ} {i k : Vertex.{u} n} (h : k < i) : IsEmpty (ConeAtMost i k) :=
  ⟨fun a => (not_le_of_gt h) ((a.val.le_maximum i a.val.mem).trans a.property)⟩

/-- A whole original subset with least and greatest vertex equal is exactly the actual terminal singleton. -/
theorem coneAtMost_self_eq {n : ℕ} {k : Vertex.{u} n} (a : ConeAtMost k k) : a = coneUpperVertex k := by
  apply Subtype.ext
  apply ConeSubset.ext
  change a.val.vertices = ({k} : Set (Vertex.{u} n)).toFinite.toFinset
  rw [Set.Finite.toFinset_singleton]
  ext j
  constructor
  · intro hj
    exact Finset.mem_singleton.mpr (le_antisymm ((a.val.le_maximum j hj).trans a.property) (a.val.lower j hj))
  · intro hj
    exact (Finset.mem_singleton.mp hj).symm ▸ a.val.mem

/-- An original coherent self path has precisely the original singleton, with no extra vertex or operator discarded. -/
theorem coneSelfPath_eq_id {n : ℕ} {k : Vertex.{u} n} (p : SimplicialThickening.Path k k) :
    p = (𝟙 (SimplicialThickening.mk k)) := by
  apply SimplicialThickening.Path.ext
  ext j
  constructor
  · intro hj
    exact Set.mem_singleton_iff.mpr (le_antisymm (p.le_right j hj) (p.left_le j hj))
  · intro hj
    exact (Set.mem_singleton_iff.mp hj).symm ▸ p.left

/-- The actual bounded singleton maps back to the original free self path and canonical point coordinate. -/
def coneUpperSelfInverse {n : ℕ} (k : Vertex.{u} n) :
    coneAtMostWeight k k ⟶ (coneUpperFreeDiagram k).obj (op (SimplicialThickening.mk k)) :=
  prodLift
    (toMax (SSet.const (nerveEquiv.symm (𝟙 (SimplicialThickening.mk k)))))
    ((parameterZeroIsTerminal .maximal).from (coneAtMostWeight k k))

/-- At the original new vertex, the full native free upper-cell map is strictly its same singleton isomorphism. -/
def coneUpperSelfIso {n : ℕ} (k : Vertex.{u} n) :
    (coneUpperFreeDiagram k).obj (op (SimplicialThickening.mk k)) ≅ coneAtMostWeight k k where
  hom := (coneUpperFreeMap k).app (op (SimplicialThickening.mk k))
  inv := coneUpperSelfInverse k
  hom_inv_id := by
    apply Hom.ext
    ext q a
    apply Prod.ext
    · refine CategoryTheory.Functor.ext (fun t => ?_) (fun _ _ _ => ?_)
      · exact (coneSelfPath_eq_id (a.1.obj t)).symm
      · apply InducedCategory.Hom.ext
        exact Subsingleton.elim _ _
    · apply SSet.stdSimplex.ext
      intro t
      exact (Fin.eq_zero _).symm
  inv_hom_id := by
    rw [coneUpperFreeMap_component]
    apply Hom.ext
    ext q a
    refine CategoryTheory.Functor.ext (fun t => ?_) (fun _ _ _ => Subsingleton.elim _ _)
    exact (coneAtMost_self_eq (a.obj t)).symm

end SSet.Marked.CoherentWeight
