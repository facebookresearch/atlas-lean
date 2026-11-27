/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Percolation.Universality.FaceDualVCrossingPinnedAnchor

/-!
# Frontier arcs in the face boundary graph

Restates the anchor condition `ccc_FrontierReachesBottom` in terms of the face boundary graph
`faceBoundaryGraph (bcd_leftReach ω n)` of the left cluster: every right-frontier face is joined
to the row-`0` frontier face by a boundary walk all of whose steps cross primal edges with both
endpoints in the box `[0, n]²` (`crc2_FrontierArcReaches`). Such walks are exactly walks in the
box face barrier (`crc2_walk_lift`), so the two conditions are equivalent under
`¬ HorizontalCrossing ω 0 n 0 n`. The arc condition is a hypothesis, not proved for general `ω`.

## Main definitions

* `crc2_IsBoxInteriorEdge n f g`: the primal edge shared by faces `f`, `g` has both endpoints in
  `[0, n]²`.
* `crc2_FrontierArcReaches ω n`: the arc condition above.

## Main results

* `crc2_walk_lift`: a face boundary walk crossing only box edges is a box face barrier walk.
* `crc2_frontierReachesBottom_of_arc`, `crc2_arc_of_atom`: equivalence with
  `ccc_FrontierReachesBottom`.
* `crc2_faceDualVCrossing_of_arc`: no horizontal crossing of `[0, n]²` together with the arc
  condition gives a face-dual vertical crossing `pmd_FaceDualVCrossing ω n`.
* `crc2_wall_frontierArcReaches`: the arc condition holds on the wall configuration.
-/

@[expose] public section

open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box

namespace StatMech

namespace Universality

/-- The primal edge shared by the faces `f` and `g` has both endpoints in the box `[0, n]²`. -/
def crc2_IsBoxInteriorEdge (n : ℤ) (f g : Site 2) : Prop :=
  ∃ p q : Site 2, sharedPrimalEdge f g = s(p, q) ∧ p ∈ rect 0 n 0 n ∧ q ∈ rect 0 n 0 n

/-- A face boundary edge crossing a box edge is an edge of the box face barrier. -/
theorem crc2_boxBarrier_adj_of_interior (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {f g : Site 2}
    (hfb : (faceBoundaryGraph (bcd_leftReach ω n)).Adj f g)
    (hint : crc2_IsBoxInteriorEdge n f g) :
    (pmd_boxFaceBarrier ω n).Adj f g := by
  obtain ⟨p, q, hpq, hp, hq⟩ := hint
  refine ⟨hfb.1, p, q, hpq, ?_, hp, hq⟩
  have := faceBoundaryGraph_sharedPrimalEdge_bdEdge _ hfb
  rwa [hpq] at this

/-- A face boundary walk all of whose steps cross box edges is a walk in the box face barrier. -/
theorem crc2_walk_lift (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {u v : Site 2}
    (w : (faceBoundaryGraph (bcd_leftReach ω n)).Walk u v)
    (hint : ∀ f g : Site 2, s(f, g) ∈ w.edges → crc2_IsBoxInteriorEdge n f g) :
    (pmd_boxFaceBarrier ω n).Reachable u v := by
  refine ⟨w.transfer (pmd_boxFaceBarrier ω n) ?_⟩
  intro e he
  refine e.ind (fun f g hfg => ?_) he
  rw [SimpleGraph.mem_edgeSet]
  exact crc2_boxBarrier_adj_of_interior ω n (w.adj_of_mem_edges hfg) (hint f g hfg)

/-- The step from a frontier face `![c, r]` down to `![c, r - 1]` crosses a box edge. -/
theorem crc2_frontier_down_edge_interior (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {c r : ℤ}
    (hr0 : 0 ≤ r) (hrn : r ≤ n) (htr : mbc_IsRightFrontier ω n c r) :
    crc2_IsBoxInteriorEdge n ![c, r] ![c, r - 1] := by
  obtain ⟨hc0, hcn, _hcL, _hmax⟩ := htr
  refine ⟨![c, r], ![c + 1, r], ?_, ?_, ?_⟩
  · rw [sharedPrimalEdge_bottom]; unfold faceCorner00 faceCorner10; rfl
  · rw [mem_rect]
    exact ⟨by simpa using hc0, by simp; omega, by simpa using hr0, by simpa using hrn⟩
  · rw [mem_rect]
    exact ⟨by simp; omega, by simp; omega, by simpa using hr0, by simpa using hrn⟩

/-- Arc condition: for the row-`0` frontier `c₀`, every right-frontier face `![c, r]`,
`r ∈ [0, n]`, is joined to `![c₀, 0]` by a face boundary walk of the left cluster crossing only
box edges. A hypothesis carrying the planar content of crossing duality. -/
def crc2_FrontierArcReaches (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) : Prop :=
  ∀ (c₀ : ℤ), mbc_IsRightFrontier ω n c₀ 0 →
    ∀ (r : ℤ), 0 ≤ r → r ≤ n → ∀ (c : ℤ), mbc_IsRightFrontier ω n c r →
      ∃ w : (faceBoundaryGraph (bcd_leftReach ω n)).Walk ![c, r] ![c₀, 0],
        ∀ f g : Site 2, s(f, g) ∈ w.edges → crc2_IsBoxInteriorEdge n f g

/-- The arc condition implies the anchor condition (given no horizontal crossing). -/
theorem crc2_frontierReachesBottom_of_arc (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (hn : 0 ≤ n)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) (harc : crc2_FrontierArcReaches ω n) :
    ccc_FrontierReachesBottom ω n := by
  obtain ⟨c₀, hc₀⟩ := mbc_exists_rightFrontier ω n hn hnoH (le_refl 0) hn
  obtain ⟨hc0, hcn, _, _⟩ := id hc₀
  refine cac_frontierReachesBottom_of_anchor ω n hc0 hcn (le_refl _) (by omega : (-1 : ℤ) ≤ n) ?_
  intro r hr0 hrn c hc
  obtain ⟨w, hw⟩ := harc c₀ hc₀ r hr0 hrn c hc
  exact (crc2_walk_lift ω n w hw).trans (cac_row0_frontier_reaches_bottom ω n hn hc₀)

/-- The anchor condition implies the arc condition. -/
theorem crc2_arc_of_atom (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (hn : 0 ≤ n)
    (h : ccc_FrontierReachesBottom ω n) : crc2_FrontierArcReaches ω n := by
  classical
  obtain ⟨a₀, b₀, _, _, _, _, hanchor⟩ := h
  intro c₀ hc₀ r hr0 hrn c hc
  have hreachA : (pmd_boxFaceBarrier ω n).Reachable ![c, r] ![a₀, b₀] := hanchor r hr0 hrn c hc
  have hreach0 : (pmd_boxFaceBarrier ω n).Reachable ![c₀, 0] ![a₀, b₀] :=
    hanchor 0 (le_refl 0) hn c₀ hc₀
  have hreach : (pmd_boxFaceBarrier ω n).Reachable ![c, r] ![c₀, 0] := hreachA.trans hreach0.symm
  obtain ⟨wb⟩ := hreach
  set wf : (faceBoundaryGraph (bcd_leftReach ω n)).Walk ![c, r] ![c₀, 0] :=
    wb.mapLe (cac_boxFaceBarrier_le_faceBoundaryGraph ω n) with hwf
  refine ⟨wf, ?_⟩
  intro f g hfg
  have hadj : (pmd_boxFaceBarrier ω n).Adj f g := by
    have hmap : wf.edges = wb.edges := by
      rw [hwf]; exact SimpleGraph.Walk.edges_mapLe_eq_edges _ _
    rw [hmap] at hfg
    exact wb.adj_of_mem_edges hfg
  obtain ⟨_hlat, p, q, hpq, _hbd, hp, hq⟩ := hadj
  exact ⟨p, q, hpq, hp, hq⟩

/-- The arc condition implies the residual hypothesis `pmd_BarrierConnectsRows` (given no
horizontal crossing). -/
theorem crc2_barrierConnectsRows_of_arc (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (hn : 0 ≤ n)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) (harc : crc2_FrontierArcReaches ω n) :
    pmd_BarrierConnectsRows ω n :=
  ccc_barrierConnectsRows_of_reachesBottom ω n hn hnoH
    (crc2_frontierReachesBottom_of_arc ω n hn hnoH harc)

/-- Conditional crossing duality: no horizontal crossing of `[0, n]²` together with the arc
condition gives a face-dual vertical crossing. -/
theorem crc2_faceDualVCrossing_of_arc (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (hn : 0 ≤ n)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) (harc : crc2_FrontierArcReaches ω n) :
    pmd_FaceDualVCrossing ω n :=
  ccc_faceDualVCrossing_of_reachesBottom ω n hn hnoH
    (crc2_frontierReachesBottom_of_arc ω n hn hnoH harc)

/-- The arc condition holds for the wall configuration. -/
theorem crc2_wall_frontierArcReaches : crc2_FrontierArcReaches bcc_wallCfg 2 :=
  crc2_arc_of_atom bcc_wallCfg 2 (by norm_num) ccc_wall_frontierReachesBottom

end Universality

end StatMech
