/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.RSWTraceSeparationObstruction
import Code.Universality.RSWCanonicalOrbitSides
















open Function MeasureTheory Set

namespace StatMech
namespace Universality

open StatMech.Percolation
open StatMech.Lattice
open StatMech.RSW.Box

noncomputable def rlc_windingSideCounterexampleGap :
    RlcAxisBarrierGap rlc_traceSplitCounterexampleRight
      rlc_traceSplitCounterexampleLeft where
  lower := -1
  upper := 1
  lower_mem := by
    rw [rlc_mem_axisHeights_iff,
      rlc_traceSplitCounterexample_right_vertices]
    simp
  upper_mem := by
    rw [rlc_mem_axisHeights_iff,
      rlc_traceSplitCounterexample_left_vertices]
    simp
  start_le := by
    have hstart : (rlc_traceSplitCounterexampleRight.1.1 : Site 2) ∈
        rlc_pathVertices rlc_traceSplitCounterexampleRight.1 := by
      exact (rlc_mem_ambientCrossingWalk_support_iff_pathVertices _ _).1
        (rlc_ambientCrossingWalk _).start_mem_support
    rw [rlc_traceSplitCounterexample_right_vertices] at hstart
    simp only [Finset.mem_insert, Finset.mem_singleton] at hstart
    rcases hstart with h | h | h | h
    · rw [h]; simp
    · rw [h]; simp
    · rw [h]; simp
    · have hx := rlc_traceSplitCounterexampleRight.1.1.2.2
      rw [h] at hx
      simp at hx
  lower_lt_upper := by omega
  upper_le_finish := by
    have hend : (rlc_traceSplitCounterexampleLeft.1.2.1 : Site 2) ∈
        rlc_pathVertices rlc_traceSplitCounterexampleLeft.1 := by
      exact (rlc_mem_ambientCrossingWalk_support_iff_pathVertices _ _).1
        (rlc_ambientCrossingWalk _).end_mem_support
    rw [rlc_traceSplitCounterexample_left_vertices] at hend
    simp only [Finset.mem_insert, Finset.mem_singleton] at hend
    rcases hend with h | h | h | h
    · have hx := rlc_traceSplitCounterexampleLeft.1.2.1.2.2
      rw [h] at hx
      simp at hx
    · rw [h]; simp
    · rw [h]; simp
    · rw [h]; simp
  interior_free := by
    intro t hlow hupp
    have ht : t = 0 := by omega
    subst t
    rw [rlc_axis_mem_connectorBarrier_iff]
    rw [rlc_traceSplitCounterexample_right_vertices,
      rlc_traceSplitCounterexample_left_vertices]
    simp

def rlc_windingSideCounterexampleConfig : ConfigSpace (Sym2 (Site 2)) :=
  fun _ => false

theorem rlc_windingSideCounterexample_failure :
    rlc_windingSideCounterexampleConfig ∉
      rlc_mixedWiredConnectorEvent rlc_windingSideCounterexampleGap := by
  let gamma := rlc_traceSplitCounterexampleRight
  let gamma' := rlc_traceSplitCounterexampleLeft
  let G := rlc_windingSideCounterexampleGap
  let omega := rlc_windingSideCounterexampleConfig
  let B := rect (-2 : ℤ) 2 (-1) 1
  let eta := rlc_wiredConnectorConfig gamma gamma'
    (rlc_mixedAxisGapEdges G) omega
  have hopen_iff (e : Sym2 (Site 2)) :
      eta e = true ↔
        e ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 := by
    simp [eta, omega, rlc_windingSideCounterexampleConfig,
      rlc_wiredConnectorConfig, rlc_maskConfig]
  have hdisj : Disjoint (rlc_pathVertices gamma.1)
      (rlc_pathVertices gamma'.1) := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    rw [show gamma = rlc_traceSplitCounterexampleRight by rfl,
      rlc_traceSplitCounterexample_right_vertices] at hz
    rw [show gamma' = rlc_traceSplitCounterexampleLeft by rfl,
      rlc_traceSplitCounterexample_left_vertices] at hz'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz hz'
    rcases hz with rfl | rfl | rfl | rfl <;> simp_all
  intro hconn
  change ConnectedWithin 2 eta B _ _ at hconn
  obtain ⟨w⟩ := hconn
  have aux {x y : B} (p : (openSubgraphInduce 2 eta B).Walk x y)
      (hx : (x : Site 2) ∈ rlc_pathVertices gamma.1) :
      (y : Site 2) ∈ rlc_pathVertices gamma.1 := by
    induction p with
    | nil => exact hx
    | @cons u v z huv p ih =>
        rw [openSubgraphInduce_adj, openSubgraph_adj] at huv
        have he := (hopen_iff s((u : Site 2), (v : Site 2))).1 huv.2
        rw [Finset.mem_union] at he
        rcases he with heRight | heLeft
        · exact ih (rlc_pathEdge_endpoints_mem_vertices gamma.1 heRight).2
        · have huLeft :=
            (rlc_pathEdge_endpoints_mem_vertices gamma'.1 heLeft).1
          exact False.elim (Finset.disjoint_left.mp hdisj hx huLeft)
  have hlower : (G.lowerVertex : Site 2) ∈
      rlc_pathVertices gamma.1 := G.lowerVertex_mem_right
  have hupperRight : (G.upperVertex : Site 2) ∈
      rlc_pathVertices gamma.1 := aux w hlower
  have hupperLeft : (G.upperVertex : Site 2) ∈
      rlc_pathVertices gamma'.1 := G.upperVertex_mem_left
  exact (Finset.disjoint_left.mp hdisj hupperRight hupperLeft)

theorem rlc_windingSideCounterexample_reachSet_eq :
    rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap
        rlc_windingSideCounterexampleConfig =
      (rlc_pathVertices rlc_traceSplitCounterexampleRight.1 : Set (Site 2)) := by
  let gamma := rlc_traceSplitCounterexampleRight
  let gamma' := rlc_traceSplitCounterexampleLeft
  let G := rlc_windingSideCounterexampleGap
  let omega := rlc_windingSideCounterexampleConfig
  let B := rect (-2 : ℤ) 2 (-1) 1
  let eta := rlc_wiredConnectorConfig gamma gamma'
    (rlc_mixedAxisGapEdges G) omega
  have hopen_iff (e : Sym2 (Site 2)) :
      eta e = true ↔
        e ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 := by
    simp [eta, omega, rlc_windingSideCounterexampleConfig,
      rlc_wiredConnectorConfig, rlc_maskConfig]
  have hdisj : Disjoint (rlc_pathVertices gamma.1)
      (rlc_pathVertices gamma'.1) := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    rw [show gamma = rlc_traceSplitCounterexampleRight by rfl,
      rlc_traceSplitCounterexample_right_vertices] at hz
    rw [show gamma' = rlc_traceSplitCounterexampleLeft by rfl,
      rlc_traceSplitCounterexample_left_vertices] at hz'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz hz'
    rcases hz with rfl | rfl | rfl | rfl <;> simp_all
  apply Set.Subset.antisymm
  · intro z hz
    obtain ⟨_hzB, hzConn⟩ := hz
    change ConnectedWithin 2 eta B _ _ at hzConn
    obtain ⟨w⟩ := hzConn
    have aux {x y : B} (p : (openSubgraphInduce 2 eta B).Walk x y)
        (hx : (x : Site 2) ∈ rlc_pathVertices gamma.1) :
        (y : Site 2) ∈ rlc_pathVertices gamma.1 := by
      induction p with
      | nil => exact hx
      | @cons u v q huv p ih =>
          rw [openSubgraphInduce_adj, openSubgraph_adj] at huv
          have he := (hopen_iff s((u : Site 2), (v : Site 2))).1 huv.2
          rw [Finset.mem_union] at he
          rcases he with heRight | heLeft
          · exact ih (rlc_pathEdge_endpoints_mem_vertices gamma.1 heRight).2
          · have huLeft :=
              (rlc_pathEdge_endpoints_mem_vertices gamma'.1 heLeft).1
            exact False.elim (Finset.disjoint_left.mp hdisj hx huLeft)
    exact aux w G.lowerVertex_mem_right
  · intro z hz
    exact rlc_rightPathVertex_mem_mixedWiredReachSet G omega hz

theorem rlc_windingSideCounterexample_right_preimages_outside_winding
    {x : Site 2}
    (hx : x ∈ rlc_pathVertices rlc_traceSplitCounterexampleRight.1) :
    rlc_primalDualReflect.symm x ∉
      rlc_outerExitWindingRegion rlc_windingSideCounterexampleGap
        rlc_windingSideCounterexampleConfig := by
  let G := rlc_windingSideCounterexampleGap
  let omega := rlc_windingSideCounterexampleConfig
  let K := rlc_mixedWiredReachSet G omega
  let a := rlc_outerExitAnchor G omega
  have hK : K =
      (rlc_pathVertices rlc_traceSplitCounterexampleRight.1 : Set (Site 2)) := by
    exact rlc_windingSideCounterexample_reachSet_eq
  have hbox : K ⊆ box 2 2 := by
    simpa [K, G] using
      (rlc_mixedWiredReachSet_subset_natBox G (by norm_num) omega)
  have hheadExt : a.1.head ∈ exterior 2 2 := by
    simpa [a, G] using
      (rlc_outerExitDart_head_mem_exterior G (by norm_num) omega)
  have hhead : a.1.head ∉ jec_leftRegion (mpl_orbitLoop K a) := by
    simpa [K, a, G, rlc_outerExitWindingRegion, mpl_orbitLoop] using
      (rlc_outerExitAnchor_head_not_mem_windingRegion G (by norm_num) omega)
  have exclude {z q : Site 2}
      (hzNot : z ∉ K) (hqNot : q ∉ K)
      (hadj : (hypercubicLattice 2).Adj q z)
      (hqExt : q ∈ exterior 2 2) :
      z ∉ rlc_outerExitWindingRegion G omega := by
    have hext : (Ising.latticeOn Kᶜ).Reachable a.1.head q :=
      rlc_latticeOn_compl_reachable_of_exterior K 2 hbox hheadExt hqExt
    have hstep : (Ising.latticeOn Kᶜ).Reachable q z :=
      (show (Ising.latticeOn Kᶜ).Adj q z from
        ⟨hadj, hqNot, hzNot⟩).reachable
    have hreach : (latticeMinusBarrier K).Reachable a.1.head z :=
      (hext.trans hstep).mono (Ising.latticeOn_compl_le_latticeMinusBarrier K)
    simpa [K, a, G, rlc_outerExitWindingRegion, mpl_orbitLoop] using
      (rlc_mpl_orbitLoop_excludes_of_head_reachable K a hhead hreach)
  have hzNot : rlc_primalDualReflect.symm x ∉ K := by
    rw [hK]
    exact (rlc_traceSplitCounterexample_right_preimage_avoids_traces hx).1
  rw [rlc_traceSplitCounterexample_right_vertices] at hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · apply exclude hzNot (q := ![0, -3])
    · rw [hK, rlc_traceSplitCounterexample_right_vertices]
      simp
    · simp [hypercubicLattice_adj, Fin.sum_univ_two,
        rlc_primalDualReflect, rlc_primalDualReflectInvFun]
    · rw [mem_exterior]
      exact ⟨1, by norm_num⟩
  · apply exclude hzNot (q := ![-1, -3])
    · rw [hK, rlc_traceSplitCounterexample_right_vertices]
      simp
    · simp [hypercubicLattice_adj, Fin.sum_univ_two,
        rlc_primalDualReflect, rlc_primalDualReflectInvFun]
    · rw [mem_exterior]
      exact ⟨1, by norm_num⟩
  · apply exclude hzNot (q := ![-2, -3])
    · rw [hK, rlc_traceSplitCounterexample_right_vertices]
      simp
    · simp [hypercubicLattice_adj, Fin.sum_univ_two,
        rlc_primalDualReflect, rlc_primalDualReflectInvFun]
    · rw [mem_exterior]
      exact ⟨1, by norm_num⟩
  · apply exclude hzNot (q := ![-3, -1])
    · rw [hK, rlc_traceSplitCounterexample_right_vertices]
      simp
    · simp [hypercubicLattice_adj, Fin.sum_univ_two,
        rlc_primalDualReflect, rlc_primalDualReflectInvFun]
    · rw [mem_exterior]
      exact ⟨0, by norm_num⟩

theorem rlc_windingSideCounterexample_not_windingSplit :
    ¬ RlcOuterExitTraceWindingSplit rlc_windingSideCounterexampleGap
      rlc_windingSideCounterexampleConfig := by
  intro hsplit
  obtain ⟨x, hx, y, hy, hxy⟩ := hsplit.1
  have hxOut :=
    rlc_windingSideCounterexample_right_preimages_outside_winding hx
  have hyOut :=
    rlc_windingSideCounterexample_right_preimages_outside_winding hy
  rcases hxy with hxy | hxy
  · exact hxOut hxy.1
  · exact hyOut hxy.2



theorem rlc_windingSideCounterexample_not_traceSeparation :
    rlc_windingSideCounterexampleConfig ∉
        rlc_mixedWiredConnectorEvent rlc_windingSideCounterexampleGap ∧
      ¬ RlcOuterExitTraceSeparation rlc_windingSideCounterexampleGap
        (by norm_num) (by change -1 + 1 < 1; omega)
          rlc_windingSideCounterexampleConfig := by
  refine ⟨rlc_windingSideCounterexample_failure, ?_⟩
  rw [rlc_outerExitTraceSeparation_iff_windingSplit]
  exact rlc_windingSideCounterexample_not_windingSplit

end Universality
end StatMech
