/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





























































import Mathlib
import Code.Lattice.JordanExteriorClosure
import Code.Lattice.WindingWitness
import Code.Walls.kwceventtocut
import Code.Walls.rpccrossflip

open Set SimpleGraph
open scoped BigOperators

namespace StatMech
namespace Walls
open StatMech.Lattice






noncomputable def ceo_shiftSquare : (hypercubicLattice 2).Walk ![0, 1] ![0, 1] :=
  let s1 : (hypercubicLattice 2).Walk ![0, 1] ![1, 1] :=
    (jec_hsegRight 1 0 1).copy (by ext i; fin_cases i <;> simp) (by ext i; fin_cases i <;> simp)
  let s2 : (hypercubicLattice 2).Walk ![1, 1] ![1, 2] :=
    (jec_vsegUp 1 1 1).copy rfl (by ext i; fin_cases i <;> simp)
  let s3 : (hypercubicLattice 2).Walk ![1, 2] ![0, 2] :=
    ((jec_hsegRight 2 0 1).copy (by ext i; fin_cases i <;> simp)
      (by ext i; fin_cases i <;> simp)).reverse
  let s4 : (hypercubicLattice 2).Walk ![0, 2] ![0, 1] :=
    ((jec_vsegUp 0 1 1).copy rfl (by ext i; fin_cases i <;> simp)).reverse
  s1.append (s2.append (s3.append s4))




theorem ceo_shiftSquare_edges_nodup : ceo_shiftSquare.edges.Nodup := by
  unfold ceo_shiftSquare
  simp [SimpleGraph.Walk.edges_cons, jec_hsegRight, jec_vsegUp]



theorem ceo_uv_adj : (hypercubicLattice 2).Adj (![0, 1] : Site 2) (![1, 1] : Site 2) := by
  simp [hypercubicLattice_adj, Fin.sum_univ_two]



theorem ceo_shiftSquare_edge_mem :
    s((![0, 1] : Site 2), (![1, 1] : Site 2)) ∈ ceo_shiftSquare.edges := by
  unfold ceo_shiftSquare
  simp [SimpleGraph.Walk.edges_cons, jec_hsegRight, jec_vsegUp]





theorem ceo_shiftSquare_crossEdge_count_zero :
    ceo_shiftSquare.edges.count (rpc_crossEdge (![0, 1] : Site 2) (![1, 1] : Site 2)) = 0 := by
  have hce : rpc_crossEdge (![0, 1] : Site 2) (![1, 1] : Site 2)
      = rpc_hCrossEdge (![0, 1] : Site 2) := by
    rw [rpc_crossEdge]; rw [if_pos]; simp
  rw [hce, rpc_hCrossEdge]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  unfold ceo_shiftSquare
  simp [SimpleGraph.Walk.edges_cons, jec_hsegRight, jec_vsegUp, List.count]










theorem ceo_shiftSquare_residue_false : ¬ rpc_CrossEdgeOddIffOnWalk ceo_shiftSquare := by
  intro h
  have hodd := (h ceo_uv_adj).mpr ceo_shiftSquare_edge_mem
  rw [ceo_shiftSquare_crossEdge_count_zero] at hodd
  exact (Nat.not_odd_iff_even.mpr (by decide)) hodd













theorem ceo_shiftSquare_rayCount_endpoints :
    jec_rayCount (![0, 1] : Site 2) ceo_shiftSquare = 0 ∧
      jec_rayCount (![1, 1] : Site 2) ceo_shiftSquare = 0 := by
  constructor <;>
    · unfold ceo_shiftSquare
      simp only [jec_rayCount_append, jec_rayCount_copy, jec_rayCount_reverse,
        jec_rayCount_vsegUp, jec_rayCount_hsegRight, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      norm_num




theorem ceo_shiftSquare_inside_odd :
    jec_rayCount (![1, 2] : Site 2) ceo_shiftSquare = 1 := by
  unfold ceo_shiftSquare
  simp only [jec_rayCount_append, jec_rayCount_copy, jec_rayCount_reverse,
    jec_rayCount_vsegUp, jec_rayCount_hsegRight, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  norm_num






theorem ceo_shiftSquare_not_bdEdge :
    ¬ bdEdge (jec_leftRegion ceo_shiftSquare) s((![0, 1] : Site 2), (![1, 1] : Site 2)) := by
  obtain ⟨h01, h11⟩ := ceo_shiftSquare_rayCount_endpoints
  rw [bdEdge_mk, jec_mem_leftRegion, jec_mem_leftRegion, h01, h11]
  simp







theorem ceo_primalWalkLeftRegionMatch_false : ¬ kwc_PrimalWalkLeftRegionMatch := by
  intro h
  have := (h ceo_shiftSquare ceo_uv_adj).mp (List.mem_toFinset.mpr ceo_shiftSquare_edge_mem)
  exact ceo_shiftSquare_not_bdEdge this

end Walls
end StatMech
