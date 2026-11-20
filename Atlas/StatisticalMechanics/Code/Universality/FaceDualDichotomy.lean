/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/







































































import Mathlib
import Code.RSW.Defs
import Code.RSW.SelfDuality
import Code.Lattice.CrossingParity
import Code.Lattice.PlanarDual
import Code.Lattice.Clusters
import Code.Lattice.FaceRegion
import Code.Lattice.JordanContour
import Code.Universality.BoxCrossingDichotomy
import Code.Universality.DualCircuitToWalk

open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box

namespace StatMech

namespace Universality

variable {ω : ConfigSpace (Sym2 (Site 2))} {n : ℤ}













theorem fdd_faceBoundary_dualEdge_isLatticeEdge {f g : Site 2}
    (h : (hypercubicLattice 2).Adj f g) :
    ∃ p q : Site 2, crossEdge (sharedPrimalEdge f g) = s(rot90Fun p, rot90Fun q) ∧
      (hypercubicLattice 2).Adj (rot90Fun p) (rot90Fun q) := by
  obtain ⟨p, q, hpq, hadj⟩ := sharedPrimalEdge_isLatticeEdge h
  exact ⟨p, q, by rw [hpq, crossEdge_mk], (rot90_adj p q).mpr hadj⟩




theorem fdd_faceBoundary_edge_dual_open (ω : ConfigSpace (Sym2 (Site 2))) {f g : Site 2}
    (hclosed : ω (sharedPrimalEdge f g) = false) :
    dualConfig ω (crossEdge (sharedPrimalEdge f g)) = true := by
  rw [StatMech.RSW.dualCross_open_iff_closed]; exact hclosed




theorem fdd_faceBoundaryGraph_dualAdj (ω : ConfigSpace (Sym2 (Site 2))) {p q : Site 2}
    (hadj : (hypercubicLattice 2).Adj p q) (hclosed : ω s(p, q) = false) :
    (openSubgraph 2 (dualConfig ω)).Adj (rot90Fun p) (rot90Fun q) := by
  refine ⟨(rot90_adj p q).mpr hadj, ?_⟩
  have : dualConfig ω (crossEdge s(p, q)) = true := by
    rw [StatMech.RSW.dualCross_open_iff_closed]; exact hclosed
  rwa [crossEdge_mk] at this
















theorem fdd_cluster_faceBoundary_edge_dual_open (o : Site 2) {f g : Site 2}
    (h : (faceBoundaryGraph (cluster 2 ω o)).Adj f g) :
    dualConfig ω (crossEdge (sharedPrimalEdge f g)) = true := by
  classical
  obtain ⟨hlat, hbd⟩ := h
  
  obtain ⟨p, q, hpq, hadj⟩ := sharedPrimalEdge_isLatticeEdge hlat
  
  rw [hpq] at hbd
  rw [bdEdge_mk] at hbd
  have hclosed : ω (sharedPrimalEdge f g) = false := by
    rw [hpq]; exact cluster_edgeBoundary_isClosed o ⟨hadj, hbd⟩
  exact fdd_faceBoundary_edge_dual_open ω (f := f) (g := g) hclosed







theorem fdd_cluster_dualCircuit_open (o : Site 2) (hfin : (cluster 2 ω o).Finite)
    {z : Site 2} (w : (hypercubicLattice 2).Walk o z) (hz : z ∉ cluster 2 ω o) :
    ∃ (u : Site 2) (c : (faceBoundaryGraph (cluster 2 ω o)).Walk u u),
      c.IsCycle ∧
      (∀ {f g : Site 2}, s(f, g) ∈ c.edges →
        dualConfig ω (crossEdge (sharedPrimalEdge f g)) = true) := by
  obtain ⟨⟨u, c, hcyc⟩, _hsep⟩ := cluster_enclosed_by_dualCircuit o hfin w hz
  refine ⟨u, c, hcyc, ?_⟩
  intro f g hfg
  exact fdd_cluster_faceBoundary_edge_dual_open o (c.adj_of_mem_edges hfg)




















theorem fdd_leftReach_barrierEdge_dualAdj (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    {v w : Site 2} (hv : v ∈ bcd_leftReach ω n) (hwbox : w ∈ rect 0 n 0 n)
    (hadj : (hypercubicLattice 2).Adj v w) (hw : w ∉ bcd_leftReach ω n) :
    (openSubgraph 2 (dualConfig ω)).Adj (rot90Fun v) (rot90Fun w) :=
  fdd_faceBoundaryGraph_dualAdj ω hadj (bcd_leftReach_boundary_closed ω n hv hwbox hadj hw)




theorem fdd_leftReach_faceBoundary_adj (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    {v w : Site 2} (hv : v ∈ bcd_leftReach ω n) (hw : w ∉ bcd_leftReach ω n)
    (hadj : (hypercubicLattice 2).Adj v w) :
    ∃ f g : Site 2, (faceBoundaryGraph (bcd_leftReach ω n)).Adj f g := by
  exact exists_faceBoundaryGraph_adj_of_edgeBoundary (bcd_leftReach ω n) (x := v) (y := w)
    ⟨hadj, iff_of_true hv hw⟩






theorem fdd_leftReach_faceBoundary_nonempty (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
    ∃ f g : Site 2, (faceBoundaryGraph (bcd_leftReach ω n)).Adj f g := by
  obtain ⟨v, w, hbar, _, _⟩ := dcw_barrierEdge_exists ω n hn hnoH
  exact fdd_leftReach_faceBoundary_adj ω n hbar.1 hbar.2.2.1 hbar.2.2.2










theorem fdd_leftReach_dualCircuit (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
    ∃ (u : Site 2) (c : (faceBoundaryGraph (bcd_leftReach ω n)).Walk u u), c.IsCycle := by
  classical
  obtain ⟨v, w, hbar, _, _⟩ := dcw_barrierEdge_exists ω n hn hnoH
  have hxy : (v, w) ∈ edgeBoundary 2 (bcd_leftReach ω n) :=
    ⟨hbar.2.2.2, iff_of_true hbar.1 hbar.2.2.1⟩
  exact exists_dualCircuit_of_finite_of_edgeBoundary (bcd_leftReach ω n)
    (bcd_leftReach_finite ω n) hxy

























theorem fdd_dualEdge_leftSide (a b : ℤ) :
    crossEdge (sharedPrimalEdge ![a, b] ![a - 1, b]) = s(![-b, a], ![-(b + 1), a]) := by
  rw [sharedPrimalEdge_left, crossEdge_mk]; unfold faceCorner00 faceCorner01
  rw [rot90Fun_apply, rot90Fun_apply]



theorem fdd_dualEdge_rightSide (a b : ℤ) :
    crossEdge (sharedPrimalEdge ![a, b] ![a + 1, b]) = s(![-b, a + 1], ![-(b + 1), a + 1]) := by
  rw [sharedPrimalEdge_right, crossEdge_mk]; unfold faceCorner10 faceCorner11
  rw [rot90Fun_apply, rot90Fun_apply]










theorem fdd_straight_dualEdges_disjoint (a b : ℤ) {p : Site 2}
    (hp1 : p ∈ crossEdge (sharedPrimalEdge ![a, b] ![a - 1, b]))
    (hp2 : p ∈ crossEdge (sharedPrimalEdge ![a, b] ![a + 1, b])) : False := by
  rw [fdd_dualEdge_leftSide] at hp1
  rw [fdd_dualEdge_rightSide] at hp2
  have h1 : p 1 = a := by
    rw [Sym2.mem_iff] at hp1; rcases hp1 with rfl | rfl <;> simp
  have h2 : p 1 = a + 1 := by
    rw [Sym2.mem_iff] at hp2; rcases hp2 with rfl | rfl <;> simp
  omega



























theorem fdd_square_dichotomy (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (hn : 0 ≤ n)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
    (bcd_leftReach ω n).Finite ∧
      (∀ {v w : Site 2}, v ∈ bcd_leftReach ω n → w ∈ rect 0 n 0 n →
        (hypercubicLattice 2).Adj v w → w ∉ bcd_leftReach ω n →
        (openSubgraph 2 (dualConfig ω)).Adj (rot90Fun v) (rot90Fun w)) ∧
      (∃ f g : Site 2, (faceBoundaryGraph (bcd_leftReach ω n)).Adj f g) ∧
      (∃ (u : Site 2) (c : (faceBoundaryGraph (bcd_leftReach ω n)).Walk u u), c.IsCycle) :=
  ⟨bcd_leftReach_finite ω n,
   fun hv hwbox hadj hw => fdd_leftReach_barrierEdge_dualAdj ω n hv hwbox hadj hw,
   fdd_leftReach_faceBoundary_nonempty ω n hn hnoH,
   fdd_leftReach_dualCircuit ω n hn hnoH⟩

end Universality

end StatMech

