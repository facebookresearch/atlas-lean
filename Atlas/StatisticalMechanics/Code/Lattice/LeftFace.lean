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
import Code.Lattice.PlanarTopology
import Code.Lattice.ContourAnchor
import Code.Lattice.EnclosingLength

open Finset Set SimpleGraph

namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}








def leftAxisSite (k : ℕ) : Site 2 := ![-(k : ℤ), 0]

@[simp] theorem leftAxisSite_zero_eq_origin : leftAxisSite 0 = origin 2 := by
  funext i; fin_cases i <;> rfl

@[simp] theorem leftAxisSite_coord0 (k : ℕ) : leftAxisSite k 0 = -(k : ℤ) := rfl
@[simp] theorem leftAxisSite_coord1 (k : ℕ) : leftAxisSite k 1 = 0 := rfl


theorem leftAxisSite_zero_mem_cluster :
    leftAxisSite 0 ∈ cluster 2 ω (origin 2) := by
  rw [leftAxisSite_zero_eq_origin]; exact self_mem_cluster ω (origin 2)


theorem exists_leftAxisSite_not_mem_cluster (hfin : (cluster 2 ω (origin 2)).Finite) :
    ∃ k : ℕ, leftAxisSite k ∉ cluster 2 ω (origin 2) := by
  by_contra hcon
  push Not at hcon
  have hinj : Function.Injective (leftAxisSite) := by
    intro a b hab
    have := congrFun hab 0
    simp only [leftAxisSite, Matrix.cons_val_zero, neg_inj, Nat.cast_inj] at this
    exact this
  have hsub : Set.range (leftAxisSite) ⊆ cluster 2 ω (origin 2) := by
    rintro x ⟨k, rfl⟩; exact hcon k
  have hran : (Set.range (leftAxisSite)).Infinite :=
    Set.infinite_range_of_injective hinj
  exact hran (hfin.subset hsub)




private def leftExitPred (ω : ConfigSpace (Sym2 (Site 2))) (k : ℕ) : Prop :=
  leftAxisSite (k + 1) ∉ cluster 2 ω (origin 2)

private theorem leftExitPred_exists (hfin : (cluster 2 ω (origin 2)).Finite) :
    ∃ k, leftExitPred ω k := by
  obtain ⟨m, hm⟩ := exists_leftAxisSite_not_mem_cluster (ω := ω) hfin
  cases m with
  | zero => exact absurd (leftAxisSite_zero_mem_cluster (ω := ω)) hm
  | succ n => exact ⟨n, hm⟩

open Classical in



noncomputable def leftExitIndex (hfin : (cluster 2 ω (origin 2)).Finite) : ℕ := by
  classical
  exact Nat.find (leftExitPred_exists (ω := ω) hfin)


theorem leftAxisSite_exit_succ_not_mem (hfin : (cluster 2 ω (origin 2)).Finite) :
    leftAxisSite (leftExitIndex (ω := ω) hfin + 1) ∉ cluster 2 ω (origin 2) := by
  classical
  exact Nat.find_spec (leftExitPred_exists (ω := ω) hfin)



theorem leftAxisSite_lt_exit_mem (hfin : (cluster 2 ω (origin 2)).Finite) {m : ℕ}
    (hm : m < leftExitIndex (ω := ω) hfin) :
    leftAxisSite (m + 1) ∈ cluster 2 ω (origin 2) := by
  classical
  have hnot : ¬ leftExitPred ω m := Nat.find_min (leftExitPred_exists (ω := ω) hfin) hm
  exact not_not.mp hnot


theorem leftAxisSite_exit_mem (hfin : (cluster 2 ω (origin 2)).Finite) :
    leftAxisSite (leftExitIndex (ω := ω) hfin) ∈ cluster 2 ω (origin 2) := by
  classical
  have hin : ∀ k, k ≤ leftExitIndex (ω := ω) hfin →
      leftAxisSite k ∈ cluster 2 ω (origin 2) := by
    intro k hk
    induction k with
    | zero => exact leftAxisSite_zero_mem_cluster (ω := ω)
    | succ m _ =>
      exact leftAxisSite_lt_exit_mem (ω := ω) hfin (Nat.lt_of_succ_le hk)
  exact hin _ le_rfl




theorem leftAxisSite_eq (k : ℕ) : (leftAxisSite k : Site 2) = ![-(k : ℤ), 0] := rfl


theorem leftAxisSite_succ_eq (k : ℕ) :
    (leftAxisSite (k + 1) : Site 2) = ![-(k : ℤ) - 1, 0] := by
  funext i; fin_cases i
  · simp only [leftAxisSite, Nat.cast_add, Nat.cast_one]
    ring_nf
  · simp [leftAxisSite]


theorem leftAxisSite_exit_adj (hfin : (cluster 2 ω (origin 2)).Finite) :
    (hypercubicLattice 2).Adj (leftAxisSite (leftExitIndex (ω := ω) hfin))
      (leftAxisSite (leftExitIndex (ω := ω) hfin + 1)) := by
  set k := leftExitIndex (ω := ω) hfin
  rw [leftAxisSite_eq k, leftAxisSite_succ_eq k]
  simp [hypercubicLattice_adj, Fin.sum_univ_two]




theorem leftExitEdge_mem_edgeBoundary (hfin : (cluster 2 ω (origin 2)).Finite) :
    (leftAxisSite (leftExitIndex (ω := ω) hfin),
        leftAxisSite (leftExitIndex (ω := ω) hfin + 1))
      ∈ edgeBoundary 2 (cluster 2 ω (origin 2)) := by
  rw [mem_edgeBoundary]
  refine ⟨leftAxisSite_exit_adj (ω := ω) hfin, ?_⟩
  rw [iff_true_intro (leftAxisSite_exit_mem (ω := ω) hfin)]
  exact iff_of_true trivial (leftAxisSite_exit_succ_not_mem (ω := ω) hfin)



theorem leftExitEdge_isClosed (hfin : (cluster 2 ω (origin 2)).Finite) :
    ω s(leftAxisSite (leftExitIndex (ω := ω) hfin),
        leftAxisSite (leftExitIndex (ω := ω) hfin + 1)) = false :=
  cluster_edgeBoundary_isClosed (origin 2) (leftExitEdge_mem_edgeBoundary (ω := ω) hfin)









noncomputable def leftExitFaceUp (hfin : (cluster 2 ω (origin 2)).Finite) : Site 2 :=
  ![-(leftExitIndex (ω := ω) hfin : ℤ) - 1, 0]


noncomputable def leftExitFaceDown (hfin : (cluster 2 ω (origin 2)).Finite) : Site 2 :=
  ![-(leftExitIndex (ω := ω) hfin : ℤ) - 1, -1]


theorem leftExitFaceUp_coord0_nonpos (hfin : (cluster 2 ω (origin 2)).Finite) :
    leftExitFaceUp (ω := ω) hfin 0 ≤ 0 := by
  show -(leftExitIndex (ω := ω) hfin : ℤ) - 1 ≤ 0
  have : (0 : ℤ) ≤ (leftExitIndex (ω := ω) hfin : ℤ) := Int.natCast_nonneg _
  omega

theorem leftExitFaceDown_coord0_nonpos (hfin : (cluster 2 ω (origin 2)).Finite) :
    leftExitFaceDown (ω := ω) hfin 0 ≤ 0 := by
  show -(leftExitIndex (ω := ω) hfin : ℤ) - 1 ≤ 0
  have : (0 : ℤ) ≤ (leftExitIndex (ω := ω) hfin : ℤ) := Int.natCast_nonneg _
  omega


theorem sharedPrimalEdge_leftExitFaces (hfin : (cluster 2 ω (origin 2)).Finite) :
    sharedPrimalEdge (leftExitFaceUp (ω := ω) hfin) (leftExitFaceDown (ω := ω) hfin)
      = s(leftAxisSite (leftExitIndex (ω := ω) hfin),
          leftAxisSite (leftExitIndex (ω := ω) hfin + 1)) := by
  have hup : (leftExitFaceUp (ω := ω) hfin : Site 2)
      = ![-(leftExitIndex (ω := ω) hfin : ℤ) - 1, 0] := rfl
  have hdown : (leftExitFaceDown (ω := ω) hfin : Site 2)
      = ![-(leftExitIndex (ω := ω) hfin : ℤ) - 1, (0 : ℤ) - 1] := by
    unfold leftExitFaceDown; funext i; fin_cases i <;> simp
  have hax0 : (leftAxisSite (leftExitIndex (ω := ω) hfin) : Site 2)
      = ![-(leftExitIndex (ω := ω) hfin : ℤ), 0] := rfl
  have hax1 : (leftAxisSite (leftExitIndex (ω := ω) hfin + 1) : Site 2)
      = ![-(leftExitIndex (ω := ω) hfin : ℤ) - 1, 0] := leftAxisSite_succ_eq _
  rw [hup, hdown, sharedPrimalEdge_bottom (-(leftExitIndex (ω := ω) hfin : ℤ) - 1) 0,
    hax0, hax1]
  unfold faceCorner00 faceCorner10
  
  rw [Sym2.eq_swap]
  have hsimp : -(leftExitIndex (ω := ω) hfin : ℤ) - 1 + 1
      = -(leftExitIndex (ω := ω) hfin : ℤ) := by ring
  rw [hsimp]


theorem leftExitFaces_adj (hfin : (cluster 2 ω (origin 2)).Finite) :
    (hypercubicLattice 2).Adj (leftExitFaceUp (ω := ω) hfin)
      (leftExitFaceDown (ω := ω) hfin) := by
  have hup : (leftExitFaceUp (ω := ω) hfin : Site 2)
      = ![-(leftExitIndex (ω := ω) hfin : ℤ) - 1, 0] := rfl
  have hdown : (leftExitFaceDown (ω := ω) hfin : Site 2)
      = ![-(leftExitIndex (ω := ω) hfin : ℤ) - 1, (0 : ℤ) - 1] := by
    unfold leftExitFaceDown; funext i; fin_cases i <;> simp
  rw [hup, hdown]
  exact latAdj_bottom (-(leftExitIndex (ω := ω) hfin : ℤ) - 1) 0





theorem leftExitFaces_faceBoundaryGraph_adj (hfin : (cluster 2 ω (origin 2)).Finite) :
    (faceBoundaryGraph (cluster 2 ω (origin 2))).Adj
      (leftExitFaceUp (ω := ω) hfin) (leftExitFaceDown (ω := ω) hfin) := by
  rw [faceBoundaryGraph_adj]
  refine ⟨leftExitFaces_adj (ω := ω) hfin, ?_⟩
  rw [sharedPrimalEdge_leftExitFaces (ω := ω) hfin, bdEdge_mk]
  refine ⟨fun _ => leftAxisSite_exit_succ_not_mem (ω := ω) hfin, fun _ => ?_⟩
  exact leftAxisSite_exit_mem (ω := ω) hfin













theorem exists_faceBoundaryGraph_leftEdge (hfin : (cluster 2 ω (origin 2)).Finite) :
    ∃ f g : Site 2, (faceBoundaryGraph (cluster 2 ω (origin 2))).Adj f g ∧
      f 0 ≤ 0 ∧ g 0 ≤ 0 :=
  ⟨leftExitFaceUp (ω := ω) hfin, leftExitFaceDown (ω := ω) hfin,
    leftExitFaces_faceBoundaryGraph_adj (ω := ω) hfin,
    leftExitFaceUp_coord0_nonpos (ω := ω) hfin,
    leftExitFaceDown_coord0_nonpos (ω := ω) hfin⟩












theorem exists_cycle_through_leftEdge (hfin : (cluster 2 ω (origin 2)).Finite) :
    ∃ (u : Site 2) (c : (faceBoundaryGraph (cluster 2 ω (origin 2))).Walk u u),
      c.IsCycle ∧
        s(leftExitFaceUp (ω := ω) hfin, leftExitFaceDown (ω := ω) hfin) ∈ c.edges := by
  obtain ⟨T, hT⟩ :=
    exists_finset_support_faceBoundaryGraph (cluster 2 ω (origin 2)) hfin
  exact EvenDegree.exists_cycle_through_edge_of_even_of_finite_support
    (faceBoundaryGraph (cluster 2 ω (origin 2))) T hT
    (degree_faceBoundaryGraph_even (cluster 2 ω (origin 2)))
    (leftExitFaces_faceBoundaryGraph_adj (ω := ω) hfin)




























theorem cycleHasLeftFace_of_cycle_through_exitFaceUp_and_leftFace
    (hfin : (cluster 2 ω (origin 2)).Finite)
    (h : ∃ (u : Site 2) (c : (faceBoundaryGraph (cluster 2 ω (origin 2))).Walk u u),
        c.IsCycle ∧ exitFaceUp (ω := ω) hfin ∈ c.support ∧ ∃ w ∈ c.support, w 0 ≤ 0) :
    CycleHasLeftFace ω hfin := by
  classical
  obtain ⟨u, c, hcyc, hup, w, hwsup, hw0⟩ := h
  
  refine ⟨c.rotate (exitFaceUp (ω := ω) hfin) hup, hcyc.rotate hup, w, ?_, hw0⟩
  
  rw [SimpleGraph.Walk.mem_support_rotate_iff]
  exact hwsup









theorem cycleHasLeftFace_of_exitFaceUp_cycle_through_leftEdge
    (hfin : (cluster 2 ω (origin 2)).Finite)
    (c : (faceBoundaryGraph (cluster 2 ω (origin 2))).Walk
        (exitFaceUp (ω := ω) hfin) (exitFaceUp (ω := ω) hfin))
    (hcyc : c.IsCycle)
    (hedge : s(leftExitFaceUp (ω := ω) hfin, leftExitFaceDown (ω := ω) hfin) ∈ c.edges) :
    CycleHasLeftFace ω hfin := by
  
  
  refine ⟨c, hcyc, leftExitFaceUp (ω := ω) hfin, c.fst_mem_support_of_mem_edges hedge,
    leftExitFaceUp_coord0_nonpos (ω := ω) hfin⟩













theorem anchoredCycleExists_of_exitFaceUp_cycle_through_leftEdge
    (hfin : (cluster 2 ω (origin 2)).Finite)
    (c : (faceBoundaryGraph (cluster 2 ω (origin 2))).Walk
        (exitFaceUp (ω := ω) hfin) (exitFaceUp (ω := ω) hfin))
    (hcyc : c.IsCycle)
    (hedge : s(leftExitFaceUp (ω := ω) hfin, leftExitFaceDown (ω := ω) hfin) ∈ c.edges) :
    AnchoredCycleExists ω hfin :=
  anchoredCycleExists_of_leftFace (ω := ω) hfin
    (cycleHasLeftFace_of_exitFaceUp_cycle_through_leftEdge (ω := ω) hfin c hcyc hedge)








theorem pcAnchoredEnclosure_of_exitFaceUp_cycle_through_leftEdge
    (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite),
        ∃ c : (faceBoundaryGraph (cluster 2 ω (origin 2))).Walk
            (exitFaceUp (ω := ω) hfin) (exitFaceUp (ω := ω) hfin),
          c.IsCycle ∧
            s(leftExitFaceUp (ω := ω) hfin, leftExitFaceDown (ω := ω) hfin) ∈ c.edges) :
    StatMech.Percolation.PcAnchoredEnclosure := by
  refine pcAnchoredEnclosure_of_cycleHasLeftFace (fun ω hfin => ?_)
  obtain ⟨c, hcyc, hedge⟩ := h ω hfin
  exact cycleHasLeftFace_of_exitFaceUp_cycle_through_leftEdge (ω := ω) hfin c hcyc hedge


































end Lattice

end StatMech
