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
import Code.Lattice.PlanarTopology
import Code.Lattice.JordanEnclosure
import Code.Lattice.FaceRegion
import Code.Lattice.CrossingParity
import Code.Percolation.PcUpperUncond

open Finset Set SimpleGraph

namespace StatMech

namespace Lattice

open StatMech.Percolation (anchorFinset origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}








def axisSite (j : ℕ) : Site 2 := ![(j : ℤ), 0]

@[simp] theorem axisSite_zero_eq_origin : axisSite 0 = origin 2 := by
  funext i; fin_cases i <;> rfl

@[simp] theorem axisSite_coord0 (j : ℕ) : axisSite j 0 = (j : ℤ) := rfl
@[simp] theorem axisSite_coord1 (j : ℕ) : axisSite j 1 = 0 := rfl


theorem axisSite_zero_mem_cluster :
    axisSite 0 ∈ cluster 2 ω (origin 2) := by
  rw [axisSite_zero_eq_origin]; exact self_mem_cluster ω (origin 2)




theorem exists_axisSite_not_mem_cluster (hfin : (cluster 2 ω (origin 2)).Finite) :
    ∃ j : ℕ, axisSite j ∉ cluster 2 ω (origin 2) := by
  by_contra hcon
  push Not at hcon
  
  have hinj : Function.Injective axisSite := by
    intro a b hab
    have := congrFun hab 0
    simpa [axisSite] using this
  have hsub : Set.range axisSite ⊆ cluster 2 ω (origin 2) := by
    rintro x ⟨j, rfl⟩; exact hcon j
  have hran : (Set.range axisSite).Infinite :=
    Set.infinite_range_of_injective hinj
  exact hran (hfin.subset hsub)




private def exitPred (ω : ConfigSpace (Sym2 (Site 2))) (j : ℕ) : Prop :=
  axisSite (j + 1) ∉ cluster 2 ω (origin 2)

private theorem exitPred_exists (hfin : (cluster 2 ω (origin 2)).Finite) :
    ∃ j, exitPred ω j := by
  obtain ⟨k, hk⟩ := exists_axisSite_not_mem_cluster (ω := ω) hfin
  
  cases k with
  | zero => exact absurd (axisSite_zero_mem_cluster (ω := ω)) hk
  | succ m => exact ⟨m, hk⟩

open Classical in





noncomputable def exitIndex (hfin : (cluster 2 ω (origin 2)).Finite) : ℕ := by
  classical
  exact Nat.find (exitPred_exists (ω := ω) hfin)


theorem axisSite_exit_succ_not_mem (hfin : (cluster 2 ω (origin 2)).Finite) :
    axisSite (exitIndex (ω := ω) hfin + 1) ∉ cluster 2 ω (origin 2) := by
  classical
  exact Nat.find_spec (exitPred_exists (ω := ω) hfin)



theorem axisSite_lt_exit_mem (hfin : (cluster 2 ω (origin 2)).Finite) {m : ℕ}
    (hm : m < exitIndex (ω := ω) hfin) :
    axisSite (m + 1) ∈ cluster 2 ω (origin 2) := by
  classical
  have hnot : ¬ exitPred ω m := Nat.find_min (exitPred_exists (ω := ω) hfin) hm
  exact not_not.mp hnot




theorem axisSite_exit_mem (hfin : (cluster 2 ω (origin 2)).Finite) :
    axisSite (exitIndex (ω := ω) hfin) ∈ cluster 2 ω (origin 2) := by
  classical
  
  have hin : ∀ k, k ≤ exitIndex (ω := ω) hfin → axisSite k ∈ cluster 2 ω (origin 2) := by
    intro k hk
    induction k with
    | zero => exact axisSite_zero_mem_cluster (ω := ω)
    | succ m _ =>
      exact axisSite_lt_exit_mem (ω := ω) hfin (Nat.lt_of_succ_le hk)
  exact hin _ le_rfl




theorem axisSite_exit_adj (hfin : (cluster 2 ω (origin 2)).Finite) :
    (hypercubicLattice 2).Adj (axisSite (exitIndex (ω := ω) hfin))
      (axisSite (exitIndex (ω := ω) hfin + 1)) := by
  set j := exitIndex (ω := ω) hfin
  have hsucc : (axisSite (j + 1) : Site 2) = ![(j : ℤ) + 1, 0] := by
    funext i; fin_cases i <;> simp [axisSite]
  rw [show (axisSite j : Site 2) = ![(j : ℤ), 0] from rfl, hsucc]
  exact latAdj_right (j : ℤ) 0




theorem axisExitEdge_mem_edgeBoundary (hfin : (cluster 2 ω (origin 2)).Finite) :
    (axisSite (exitIndex (ω := ω) hfin), axisSite (exitIndex (ω := ω) hfin + 1))
      ∈ edgeBoundary 2 (cluster 2 ω (origin 2)) := by
  rw [mem_edgeBoundary]
  refine ⟨axisSite_exit_adj (ω := ω) hfin, ?_⟩
  rw [iff_true_intro (axisSite_exit_mem (ω := ω) hfin)]
  exact iff_of_true trivial (axisSite_exit_succ_not_mem (ω := ω) hfin)



theorem axisExitEdge_isClosed (hfin : (cluster 2 ω (origin 2)).Finite) :
    ω s(axisSite (exitIndex (ω := ω) hfin), axisSite (exitIndex (ω := ω) hfin + 1)) = false :=
  cluster_edgeBoundary_isClosed (origin 2) (axisExitEdge_mem_edgeBoundary (ω := ω) hfin)









noncomputable def exitFaceUp (hfin : (cluster 2 ω (origin 2)).Finite) : Site 2 :=
  ![(exitIndex (ω := ω) hfin : ℤ), 0]


noncomputable def exitFaceDown (hfin : (cluster 2 ω (origin 2)).Finite) : Site 2 :=
  ![(exitIndex (ω := ω) hfin : ℤ), -1]


theorem sharedPrimalEdge_exitFaces (hfin : (cluster 2 ω (origin 2)).Finite) :
    sharedPrimalEdge (exitFaceUp (ω := ω) hfin) (exitFaceDown (ω := ω) hfin)
      = s(axisSite (exitIndex (ω := ω) hfin), axisSite (exitIndex (ω := ω) hfin + 1)) := by
  
  have hup : (exitFaceUp (ω := ω) hfin : Site 2)
      = ![(exitIndex (ω := ω) hfin : ℤ), 0] := rfl
  have hdown : (exitFaceDown (ω := ω) hfin : Site 2)
      = ![(exitIndex (ω := ω) hfin : ℤ), (0 : ℤ) - 1] := by
    unfold exitFaceDown; funext i; fin_cases i <;> simp
  have hax0 : (axisSite (exitIndex (ω := ω) hfin) : Site 2)
      = ![(exitIndex (ω := ω) hfin : ℤ), 0] := rfl
  have hax1 : (axisSite (exitIndex (ω := ω) hfin + 1) : Site 2)
      = ![(exitIndex (ω := ω) hfin : ℤ) + 1, 0] := by
    funext i; fin_cases i <;> simp [axisSite]
  rw [hup, hdown, sharedPrimalEdge_bottom (exitIndex (ω := ω) hfin : ℤ) 0,
    hax0, hax1]
  unfold faceCorner00 faceCorner10
  rfl


theorem exitFaces_adj (hfin : (cluster 2 ω (origin 2)).Finite) :
    (hypercubicLattice 2).Adj (exitFaceUp (ω := ω) hfin) (exitFaceDown (ω := ω) hfin) := by
  have hup : (exitFaceUp (ω := ω) hfin : Site 2)
      = ![(exitIndex (ω := ω) hfin : ℤ), 0] := rfl
  have hdown : (exitFaceDown (ω := ω) hfin : Site 2)
      = ![(exitIndex (ω := ω) hfin : ℤ), (0 : ℤ) - 1] := by
    unfold exitFaceDown; funext i; fin_cases i <;> simp
  rw [hup, hdown]
  exact latAdj_bottom (exitIndex (ω := ω) hfin : ℤ) 0





theorem exitFaces_faceBoundaryGraph_adj (hfin : (cluster 2 ω (origin 2)).Finite) :
    (faceBoundaryGraph (cluster 2 ω (origin 2))).Adj
      (exitFaceUp (ω := ω) hfin) (exitFaceDown (ω := ω) hfin) := by
  rw [faceBoundaryGraph_adj]
  refine ⟨exitFaces_adj (ω := ω) hfin, ?_⟩
  rw [sharedPrimalEdge_exitFaces (ω := ω) hfin, bdEdge_mk]
  refine ⟨fun _ => axisSite_exit_succ_not_mem (ω := ω) hfin, fun _ => ?_⟩
  exact axisSite_exit_mem (ω := ω) hfin








theorem exitFaceUp_mem_anchorFinset (hfin : (cluster 2 ω (origin 2)).Finite) {m : ℕ}
    (hm : exitIndex (ω := ω) hfin < m) :
    exitFaceUp (ω := ω) hfin ∈ anchorFinset m := by
  classical
  unfold anchorFinset
  rw [Finset.mem_union]
  left
  rw [Finset.mem_image]
  exact ⟨exitIndex (ω := ω) hfin, Finset.mem_range.mpr hm, rfl⟩


theorem exitFaceDown_mem_anchorFinset (hfin : (cluster 2 ω (origin 2)).Finite) {m : ℕ}
    (hm : exitIndex (ω := ω) hfin < m) :
    exitFaceDown (ω := ω) hfin ∈ anchorFinset m := by
  classical
  unfold anchorFinset
  rw [Finset.mem_union]
  right
  rw [Finset.mem_image]
  exact ⟨exitIndex (ω := ω) hfin, Finset.mem_range.mpr hm, rfl⟩
















theorem exists_anchored_faceBoundary_edge (hfin : (cluster 2 ω (origin 2)).Finite) :
    ∃ (j : ℕ) (f g : Site 2),
      (faceBoundaryGraph (cluster 2 ω (origin 2))).Adj f g ∧
      (∀ m : ℕ, j < m → f ∈ anchorFinset m ∧ g ∈ anchorFinset m) := by
  refine ⟨exitIndex (ω := ω) hfin, exitFaceUp (ω := ω) hfin, exitFaceDown (ω := ω) hfin,
    exitFaces_faceBoundaryGraph_adj (ω := ω) hfin, fun m hm =>
      ⟨exitFaceUp_mem_anchorFinset (ω := ω) hfin hm,
       exitFaceDown_mem_anchorFinset (ω := ω) hfin hm⟩⟩












theorem exists_cycle_through_exitEdge (hfin : (cluster 2 ω (origin 2)).Finite) :
    ∃ (u : Site 2) (c : (faceBoundaryGraph (cluster 2 ω (origin 2))).Walk u u),
      c.IsCycle ∧
        s(exitFaceUp (ω := ω) hfin, exitFaceDown (ω := ω) hfin) ∈ c.edges := by
  obtain ⟨T, hT⟩ :=
    exists_finset_support_faceBoundaryGraph (cluster 2 ω (origin 2)) hfin
  exact EvenDegree.exists_cycle_through_edge_of_even_of_finite_support
    (faceBoundaryGraph (cluster 2 ω (origin 2))) T hT
    (degree_faceBoundaryGraph_even (cluster 2 ω (origin 2)))
    (exitFaces_faceBoundaryGraph_adj (ω := ω) hfin)





theorem exists_cycle_based_exitFaceUp (hfin : (cluster 2 ω (origin 2)).Finite) :
    ∃ (c : (faceBoundaryGraph (cluster 2 ω (origin 2))).Walk
        (exitFaceUp (ω := ω) hfin) (exitFaceUp (ω := ω) hfin)),
      c.IsCycle := by
  classical
  obtain ⟨u, c, hcyc, hedge⟩ := exists_cycle_through_exitEdge (ω := ω) hfin
  
  have hsup : exitFaceUp (ω := ω) hfin ∈ c.support :=
    c.fst_mem_support_of_mem_edges hedge
  exact ⟨c.rotate (exitFaceUp (ω := ω) hfin) hsup, hcyc.rotate hsup⟩




























def AnchoredCycleExists (ω : ConfigSpace (Sym2 (Site 2)))
    (hfin : (cluster 2 ω (origin 2)).Finite) : Prop :=
  ∃ c : (faceBoundaryGraph (cluster 2 ω (origin 2))).Walk
      (exitFaceUp (ω := ω) hfin) (exitFaceUp (ω := ω) hfin),
    c.IsCycle ∧ exitIndex (ω := ω) hfin < c.length









theorem anchoredEnclosure_of_anchoredCycle (hfin : (cluster 2 ω (origin 2)).Finite)
    (hwind : AnchoredCycleExists ω hfin) :
    ∃ (u : Site 2) (c : (faceBoundaryGraph (cluster 2 ω (origin 2))).Walk u u),
      c.IsCycle ∧ u ∈ anchorFinset c.length := by
  obtain ⟨c, hcyc, hlen⟩ := hwind
  exact ⟨exitFaceUp (ω := ω) hfin, c, hcyc,
    exitFaceUp_mem_anchorFinset (ω := ω) hfin hlen⟩








theorem pcAnchoredEnclosure_of_anchoredCycle
    (hwind : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite),
        AnchoredCycleExists ω hfin) :
    StatMech.Percolation.PcAnchoredEnclosure := by
  intro ω hω
  exact anchoredEnclosure_of_anchoredCycle (ω := ω) hω (hwind ω hω)





































end Lattice

end StatMech
