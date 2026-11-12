/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


































































import Mathlib
import Code.Foundations.ConfigSpace
import Code.Lattice.HypercubicLattice
import Code.Lattice.PlanarDual
import Code.Lattice.Clusters
import Code.Lattice.JordanZ2
import Code.Lattice.JordanEnclosure

open Finset Set SimpleGraph

namespace StatMech

namespace Lattice






noncomputable def bdEdgeSet2 (S : Set (Site 2)) : Set (Sym2 (Site 2)) := by
  classical
  exact {e | Sym2.lift ⟨fun x y => (x ∈ S ↔ y ∉ S), by
    intro x y
    simp only [eq_iff_iff]
    by_cases hx : x ∈ S <;> by_cases hy : y ∈ S <;> tauto⟩ e}

@[simp] theorem mem_bdEdgeSet2 (S : Set (Site 2)) (x y : Site 2) :
    s(x, y) ∈ bdEdgeSet2 S ↔ (x ∈ S ↔ y ∉ S) := by
  unfold bdEdgeSet2
  rw [Set.mem_setOf_eq]
  rfl




noncomputable def cutLattice (S : Set (Site 2)) : SimpleGraph (Site 2) :=
  (hypercubicLattice 2).deleteEdges (bdEdgeSet2 S)

@[simp] theorem cutLattice_adj (S : Set (Site 2)) (x y : Site 2) :
    (cutLattice S).Adj x y ↔ (hypercubicLattice 2).Adj x y ∧ s(x, y) ∉ bdEdgeSet2 S := by
  rw [cutLattice, deleteEdges_adj]


theorem cutLattice_le (S : Set (Site 2)) : cutLattice S ≤ hypercubicLattice 2 := by
  rw [cutLattice]; exact deleteEdges_le _



theorem cutLattice_adj_of_both_mem (S : Set (Site 2)) {x y : Site 2}
    (hadj : (hypercubicLattice 2).Adj x y) (hx : x ∈ S) (hy : y ∈ S) :
    (cutLattice S).Adj x y := by
  rw [cutLattice_adj]
  refine ⟨hadj, ?_⟩
  rw [mem_bdEdgeSet2]
  tauto






theorem cutLattice_adj_preserves (S : Set (Site 2)) {x y : Site 2}
    (hadj : (cutLattice S).Adj x y) (hx : x ∈ S) : y ∈ S := by
  rw [cutLattice_adj] at hadj
  obtain ⟨_, hne⟩ := hadj
  by_contra hy
  exact hne ((mem_bdEdgeSet2 S x y).mpr ⟨fun _ => hy, fun _ => hx⟩)




theorem cutLattice_walk_preserves (S : Set (Site 2)) {x y : Site 2}
    (w : (cutLattice S).Walk x y) (hx : x ∈ S) : y ∈ S := by
  induction w with
  | nil => exact hx
  | @cons a b c hab _ ih => exact ih (cutLattice_adj_preserves S hab hx)




theorem cutLattice_reachable_preserves (S : Set (Site 2)) {x y : Site 2}
    (h : (cutLattice S).Reachable x y) (hx : x ∈ S) : y ∈ S := by
  obtain ⟨w⟩ := h
  exact cutLattice_walk_preserves S w hx





theorem cutLattice_not_reachable (S : Set (Site 2)) {x y : Site 2}
    (hx : x ∈ S) (hy : y ∉ S) : ¬ (cutLattice S).Reachable x y := by
  intro h
  exact hy (cutLattice_reachable_preserves S h hx)



variable {ω : ConfigSpace (Sym2 (Site 2))}




theorem openWalk_to_cutLattice (o : Site 2) {x y : Site 2}
    (w : (openSubgraph 2 ω).Walk x y) (hx : x ∈ cluster 2 ω o) :
    (cutLattice (cluster 2 ω o)).Reachable x y := by
  induction w with
  | nil => exact Reachable.refl _
  | @cons a b c hab _ ih =>
    have hb : b ∈ cluster 2 ω o := hx.trans (IsOpenEdge.connected hab)
    exact ((cutLattice_adj_of_both_mem _ hab.1 hx hb).reachable).trans (ih hb)




theorem cutLattice_reachable_of_connected (o : Site 2) {x : Site 2}
    (hx : x ∈ cluster 2 ω o) : (cutLattice (cluster 2 ω o)).Reachable o x := by
  obtain ⟨w⟩ := (hx : (openSubgraph 2 ω).Reachable o x)
  exact openWalk_to_cutLattice o w (self_mem_cluster ω o)




def insideRegion (ω : ConfigSpace (Sym2 (Site 2))) (o : Site 2) : Set (Site 2) :=
  {x | (cutLattice (cluster 2 ω o)).Reachable o x}

@[simp] theorem mem_insideRegion {o x : Site 2} :
    x ∈ insideRegion ω o ↔ (cutLattice (cluster 2 ω o)).Reachable o x := Iff.rfl





theorem insideRegion_eq_cluster (o : Site 2) :
    insideRegion ω o = cluster 2 ω o := by
  ext x
  rw [mem_insideRegion]
  constructor
  · intro h
    exact cutLattice_reachable_preserves _ h (self_mem_cluster ω o)
  · intro h
    exact cutLattice_reachable_of_connected o h


theorem origin_mem_insideRegion (o : Site 2) : o ∈ insideRegion ω o := by
  rw [insideRegion_eq_cluster]; exact self_mem_cluster ω o




theorem insideRegion_finite (o : Site 2) (hfin : (cluster 2 ω o).Finite) :
    (insideRegion ω o).Finite := by
  rw [insideRegion_eq_cluster]; exact hfin




theorem exists_outside_far (S : Set (Site 2)) (hS : S.Finite) (n : ℕ) :
    ∃ x : Site 2, x ∉ box 2 n ∧ x ∉ S := by
  have hfin : (box 2 n ∪ S).Finite := (box_finite 2 n).union hS
  obtain ⟨x, hx⟩ : ((box 2 n ∪ S)ᶜ).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty, compl_empty_iff] at h
    rw [h] at hfin
    exact Set.infinite_univ.not_finite hfin
  rw [Set.mem_compl_iff, Set.mem_union] at hx
  push Not at hx
  exact ⟨x, hx.1, hx.2⟩




theorem exists_outsideRegion_far (o : Site 2) (hfin : (cluster 2 ω o).Finite) (n : ℕ) :
    ∃ x : Site 2, x ∉ box 2 n ∧ x ∉ insideRegion ω o := by
  obtain ⟨x, hbox, hS⟩ := exists_outside_far (cluster 2 ω o) hfin n
  exact ⟨x, hbox, by rw [insideRegion_eq_cluster]; exact hS⟩





theorem origin_separated_from_outside (o : Site 2) {z : Site 2}
    (hz : z ∉ cluster 2 ω o) :
    ¬ (cutLattice (cluster 2 ω o)).Reachable o z :=
  cutLattice_not_reachable _ (self_mem_cluster ω o) hz





theorem origin_separated_from_far (o : Site 2) (hfin : (cluster 2 ω o).Finite) (n : ℕ) :
    ∃ z : Site 2, z ∉ box 2 n ∧ ¬ (cutLattice (cluster 2 ω o)).Reachable o z := by
  obtain ⟨z, hbox, hS⟩ := exists_outside_far (cluster 2 ω o) hfin n
  exact ⟨z, hbox, origin_separated_from_outside o hS⟩




theorem exists_two_cutComponents (o : Site 2) (hfin : (cluster 2 ω o).Finite) :
    ∃ z : Site 2, (cutLattice (cluster 2 ω o)).connectedComponentMk z
      ≠ (cutLattice (cluster 2 ω o)).connectedComponentMk o := by
  obtain ⟨z, _, hz⟩ := origin_separated_from_far o hfin 0
  refine ⟨z, ?_⟩
  intro hcontra
  rw [ConnectedComponent.eq] at hcontra
  exact hz hcontra.symm





theorem bdEdgeSet2_to_edgeBoundary (S : Set (Site 2)) {x y : Site 2}
    (hadj : (hypercubicLattice 2).Adj x y) (hmem : s(x, y) ∈ bdEdgeSet2 S) :
    (x, y) ∈ edgeBoundary 2 S := by
  rw [mem_bdEdgeSet2] at hmem
  exact ⟨hadj, hmem⟩



theorem cluster_cutEdge_isClosed (o : Site 2) {x y : Site 2}
    (hadj : (hypercubicLattice 2).Adj x y)
    (hmem : s(x, y) ∈ bdEdgeSet2 (cluster 2 ω o)) :
    ω s(x, y) = false :=
  cluster_edgeBoundary_isClosed o (bdEdgeSet2_to_edgeBoundary _ hadj hmem)




theorem cluster_cutEdge_crosses_dual_open (o : Site 2) {x y : Site 2}
    (hadj : (hypercubicLattice 2).Adj x y)
    (hmem : s(x, y) ∈ bdEdgeSet2 (cluster 2 ω o)) :
    dualConfig ω (crossEdge s(x, y)) = true :=
  cluster_edgeBoundary_crosses_dual_open o (bdEdgeSet2_to_edgeBoundary _ hadj hmem)





















theorem cluster_isBoundedRegion_separated_by_boundary (o : Site 2)
    (hfin : (cluster 2 ω o).Finite) {z₀ : Site 2}
    (w : (hypercubicLattice 2).Walk o z₀) (hz₀ : z₀ ∉ cluster 2 ω o) :
    (insideRegion ω o = cluster 2 ω o ∧ (insideRegion ω o).Finite)
      ∧ (∀ z ∉ cluster 2 ω o, ¬ (cutLattice (cluster 2 ω o)).Reachable o z)
      ∧ (∀ n : ℕ, ∃ z : Site 2,
          z ∉ box 2 n ∧ ¬ (cutLattice (cluster 2 ω o)).Reachable o z)
      ∧ (∃ (u : Site 2) (c : (faceBoundaryGraph (cluster 2 ω o)).Walk u u), c.IsCycle) := by
  refine ⟨⟨insideRegion_eq_cluster o, insideRegion_finite o hfin⟩,
    fun z hz => origin_separated_from_outside o hz,
    fun n => origin_separated_from_far o hfin n,
    exists_dualCircuit_of_finite_cluster o hfin w hz₀⟩

end Lattice

end StatMech
