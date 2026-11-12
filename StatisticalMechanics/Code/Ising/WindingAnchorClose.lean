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
import Code.Lattice.CrossingParity
import Code.Lattice.ContourAnchor
import Code.Lattice.EnclosingLength
import Code.Lattice.MinimalPeriodLoop
import Code.Lattice.AnchoredCycleClose
import Code.Lattice.ContourCountInjection
import Code.Lattice.PeierlsContourClose2
import Code.Lattice.PeierlsAnchorEncode
import Code.Ising.PeierlsUncond

open Finset Set SimpleGraph

namespace StatMech

namespace Ising

open StatMech.Lattice
open StatMech.Percolation (origin)

attribute [local instance] Classical.propDecidable

variable {ω : ConfigSpace (Sym2 (Site 2))}














theorem wac_cycle_length_le_contourLen {S : Set (Site 2)} {n : ℕ}
    (hSbox : S ⊆ box 2 n) {u : Site 2}
    (c : (faceBoundaryGraph S).Walk u u) (hcyc : c.IsCycle) :
    c.length ≤ contourLen S (bondFinsetTouch 2 n) := by
  classical
  
  have hnodup : c.edges.Nodup := hcyc.isCircuit.isTrail.edges_nodup
  have hlen : c.length = c.edges.toFinset.card := by
    rw [← SimpleGraph.Walk.length_edges, List.toFinset_card_of_nodup hnodup]
  
  have himg : Finset.image symPrimalSym c.edges.toFinset
      ⊆ crossEdges S (bondFinsetTouch 2 n) := by
    intro pe hpe
    rw [Finset.mem_image] at hpe
    obtain ⟨de, hde, rfl⟩ := hpe
    rw [List.mem_toFinset] at hde
    have hdmem : de ∈ (faceBoundaryGraph S).edgeSet :=
      c.edges_subset_edgeSet hde
    
    have hbd : symPrimalSym de ∈ boundaryEdgeSet S :=
      symPrimalSym_mem_boundaryEdgeSet hdmem
    rw [← Finset.mem_coe, coe_crossEdges_eq_boundaryEdgeSet hSbox]
    exact hbd
  
  have hinj : Set.InjOn symPrimalSym (c.edges.toFinset : Set (Sym2 (Site 2))) := by
    refine (symPrimalSym_injOn_edges S).mono ?_
    intro e he
    rw [Finset.mem_coe, List.mem_toFinset] at he
    exact c.edges_subset_edgeSet he
  calc c.length = c.edges.toFinset.card := hlen
    _ = (Finset.image symPrimalSym c.edges.toFinset).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ (crossEdges S (bondFinsetTouch 2 n)).card :=
        Finset.card_le_card himg
    _ = contourLen S (bondFinsetTouch 2 n) := rfl











theorem wac_exitFaceUp_eq_axisVertex (hfin : (cluster 2 ω (origin 2)).Finite) :
    exitFaceUp (ω := ω) hfin = axisVertex 2 (exitIndex (ω := ω) hfin) := by
  funext i
  fin_cases i <;> simp [exitFaceUp, axisVertex]











@[simp] theorem wac_axisVertex_coord0 (j : ℕ) : (axisVertex 2 j) 0 = (j : ℤ) := by
  simp [axisVertex]






theorem wac_lt_length_of_leftFace {K : Set (Site 2)} {j : ℕ}
    (c : (faceBoundaryGraph K).Walk (axisVertex 2 j) (axisVertex 2 j)) (hcyc : c.IsCycle)
    {w : Site 2} (hwsup : w ∈ c.support) (hw0 : w 0 ≤ 0) :
    j < c.length := by
  classical
  
  have h3 : 3 ≤ c.length := hcyc.three_le_length
  rcases Nat.eq_zero_or_pos j with hj | hj
  · omega
  · 
    have hdist : (j : ℕ) ≤ l1dist 2 (axisVertex 2 j) w := by
      unfold l1dist
      rw [Fin.sum_univ_two, wac_axisVertex_coord0]
      
      omega
    have hge : 2 * l1dist 2 (axisVertex 2 j) w ≤ c.length :=
      closedWalk_length_ge_two_l1dist (faceBoundaryGraph_le K) c hwsup
    omega












theorem wac_axisAnchor_of_windingCycle {S : Set (Site 2)} {n : ℕ}
    (hSbox : S ⊆ box 2 n) (hfin : S.Finite) {j : ℕ}
    (c : (faceBoundaryGraph S).Walk (axisVertex 2 j) (axisVertex 2 j))
    (hcyc : c.IsCycle) {w : Site 2} (hwsup : w ∈ c.support) (hw0 : w 0 ≤ 0) :
    ∃ (T : Finset (Site 2)) (j' : ℕ),
      (faceBoundaryGraph S).support ⊆ (T : Set (Site 2)) ∧
      j' < contourLen S (bondFinsetTouch 2 n) ∧
      axisVertex 2 j' ∈ T := by
  classical
  
  have hlt : j < c.length := wac_lt_length_of_leftFace c hcyc hwsup hw0
  have hle : c.length ≤ contourLen S (bondFinsetTouch 2 n) :=
    wac_cycle_length_le_contourLen hSbox c hcyc
  refine ⟨boundarySupport hfin, j, boundarySupport_spec hfin, lt_of_lt_of_le hlt hle, ?_⟩
  
  
  have hnotnil : ¬ c.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]; omega
  obtain ⟨v, hadj, q, _hq⟩ := SimpleGraph.Walk.not_nil_iff.mp hnotnil
  have hbase : axisVertex 2 j ∈ (faceBoundaryGraph S).support :=
    hadj.mem_support_left
  exact boundarySupport_spec hfin hbase






















theorem wac_axisAnchor_of_exitDartWinds (hfin : (cluster 2 ω (origin 2)).Finite)
    (hwind : acc_ExitDartWinds ω hfin) :
    ∃ (n : ℕ) (T : Finset (Site 2)) (j : ℕ),
      (faceBoundaryGraph (cluster 2 ω (origin 2))).support ⊆ (T : Set (Site 2)) ∧
      j < contourLen (cluster 2 ω (origin 2)) (bondFinsetTouch 2 n) ∧
      axisVertex 2 j ∈ T := by
  classical
  
  have hlf : CycleHasLeftFace ω hfin :=
    acc_cycleHasLeftFace_of_oddOrigin (ω := ω) hfin hwind.1 hwind.2
  obtain ⟨c, hcyc, w, hwsup, hw0⟩ := hlf
  
  obtain ⟨R, hRbox⟩ := finite_subset_box (cluster 2 ω (origin 2)) hfin
  
  have hbaseeq : exitFaceUp (ω := ω) hfin = axisVertex 2 (exitIndex (ω := ω) hfin) :=
    wac_exitFaceUp_eq_axisVertex (ω := ω) hfin
  have hcyc' : (c.copy hbaseeq hbaseeq).IsCycle := by
    rw [SimpleGraph.Walk.isCycle_copy]; exact hcyc
  have hwsup' : w ∈ (c.copy hbaseeq hbaseeq).support := by
    rw [SimpleGraph.Walk.support_copy]; exact hwsup
  
  obtain ⟨T, j, hsupp, hj, hax⟩ :=
    wac_axisAnchor_of_windingCycle hRbox hfin (c.copy hbaseeq hbaseeq) hcyc' hwsup' hw0
  exact ⟨R, T, j, hsupp, hj, hax⟩











theorem wac_unitCell_base_eq_axisVertex : dartFace ucBase.1 = axisVertex 2 0 := by
  funext i; fin_cases i <;> rfl







theorem wac_unitCell_axisAnchor :
    ∃ (T : Finset (Site 2)) (j : ℕ),
      (faceBoundaryGraph unitCell).support ⊆ (T : Set (Site 2)) ∧
      j < contourLen unitCell (bondFinsetTouch 2 0) ∧
      axisVertex 2 j ∈ T := by
  classical
  
  have hbox : unitCell ⊆ box 2 0 := by
    unfold unitCell StatMech.Lattice.box
    rw [Set.singleton_subset_iff]; intro i; fin_cases i <;> simp
  have hfin : (unitCell : Set (Site 2)).Finite := by unfold unitCell; exact Set.finite_singleton _
  
  have hbaseeq : dartFace ucBase.1 = axisVertex 2 0 := wac_unitCell_base_eq_axisVertex
  have hcyc : (mpl_orbitFaceLoop unitCell ucBase).IsCycle := acc_unitCell_faceLoop_isCycle
  
  obtain ⟨f, hf, hf0⟩ := acc_unitCell_hasLeftSupportFace
  rw [mpl_orbitLoop_support] at hf
  
  have hcyc' : ((mpl_orbitFaceLoop unitCell ucBase).copy hbaseeq hbaseeq).IsCycle := by
    rw [SimpleGraph.Walk.isCycle_copy]; exact hcyc
  have hf' : f ∈ ((mpl_orbitFaceLoop unitCell ucBase).copy hbaseeq hbaseeq).support := by
    rw [SimpleGraph.Walk.support_copy]; exact hf
  exact wac_axisAnchor_of_windingCycle hbox hfin
    ((mpl_orbitFaceLoop unitCell ucBase).copy hbaseeq hbaseeq) hcyc' hf' (by omega)

end Ising

end StatMech
