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
import Code.Lattice.JordanEnclosure
import Code.Universality.JordanExhaustivityClose
import Code.Universality.DualCutToPath
import Code.Universality.DualCircuitToWalk
import Code.Universality.PlanarDualCutConnected
import Code.Universality.FaceDualDichotomy
import Code.Universality.FrameChangeIso
import Code.Universality.BoxCrossingDichotomyClose

open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box

namespace StatMech

namespace Universality













theorem rdv_box_frame_target_false :
    ¬ (∀ ω : ConfigSpace (Sym2 (Site 2)),
        ¬ HorizontalCrossing ω 0 2 0 2 → DualVerticalCrossing ω 0 2 0 2) := by
  intro h
  exact bcc_noV_wall (h bcc_wallCfg bcc_noH_wall)





theorem rdv_jex_dualBarrierVCrossing_unprovable_from_noH :
    ¬ (∀ ω : ConfigSpace (Sym2 (Site 2)),
        ¬ HorizontalCrossing ω 0 2 0 2 → jex_DualBarrierVCrossing ω 2) :=
  rdv_box_frame_target_false



theorem rdv_witness_noH : ¬ HorizontalCrossing bcc_wallCfg 0 2 0 2 :=
  bcc_noH_wall



theorem rdv_witness_no_boxFrame_dualV : ¬ jex_DualBarrierVCrossing bcc_wallCfg 2 :=
  bcc_noV_wall























theorem rdv_leftReach_wall_x0 {v : Site 2} (h : v ∈ bcd_leftReach bcc_wallCfg 2) :
    v 0 = 0 := by
  obtain ⟨_hvbox, x, hxL, hvbox', hconn⟩ := h
  have hx0 : x 0 = 0 := hxL.2
  have hinv := bcc_wall_walk_keeps_x0 (x := ⟨x, leftSide_subset hxL⟩) (y := ⟨v, hvbox'⟩)
    hconn.some
  exact hinv.mp hx0






theorem rdv_barrier_wall_snd_le {p q : Site 2}
    (h : (dcw_dualBarrierGraph bcc_wallCfg 2).Adj p q) : p 1 ≤ 1 := by
  obtain ⟨v, w, ⟨hvL, hwbox, hwnL, hadj⟩, hpq⟩ := h
  have hv0 : v 0 = 0 := rdv_leftReach_wall_x0 hvL
  have hw0 : w 0 = 1 := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
    rw [hv0] at hadj
    rw [mem_rect] at hwbox
    have hw0ne : w 0 ≠ 0 := fun hw00 => hwnL
      (jex_leftSide_subset_leftReach bcc_wallCfg 2 ⟨by rw [mem_rect]; omega, hw00⟩)
    omega
  have hrv1 : (rot90Fun v) 1 = v 0 := by simp [rot90Fun]
  have hrw1 : (rot90Fun w) 1 = w 0 := by simp [rot90Fun]
  rcases hpq with ⟨hp, _⟩ | ⟨hp, _⟩
  · rw [hp, hrv1, hv0]; norm_num
  · rw [hp, hrw1, hw0]



theorem rdv_barrier_wall_walk_snd_le {p q : Site 2}
    (c : (dcw_dualBarrierGraph bcc_wallCfg 2).Walk p q) (hp : p 1 ≤ 1) : q 1 ≤ 1 := by
  induction c with
  | nil => exact hp
  | @cons a b d hab _tail ih => exact ih (rdv_barrier_wall_snd_le hab.symm)













theorem rdv_rotResidue_false_on_noH : ¬ dcp_DualCutConnectsRot bcc_wallCfg 2 := by
  rintro ⟨p₀, hp₀, q₀, hq₀, hreach⟩
  have hp0 : p₀ 1 = 0 := hp₀.2
  have hq2 : q₀ 1 = 2 := hq₀.2
  obtain ⟨c⟩ := hreach
  have hend := rdv_barrier_wall_walk_snd_le c (by rw [hp0]; norm_num)
  rw [hq2] at hend; norm_num at hend






theorem rdv_rotated_dualVerticalCrossing_of_rotResidue (ω : ConfigSpace (Sym2 (Site 2)))
    (n : ℤ) (h : dcp_DualCutConnectsRot ω n) :
    DualVerticalCrossing ω (-n) 0 0 n :=
  dcp_rotatedDualVerticalCrossing_of_cutConnectsRot ω n h












theorem rdv_exists_dualCircuit (ω : ConfigSpace (Sym2 (Site 2)))
    {n : ℤ} (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    {c : ℤ} (hc0 : 0 ≤ c) (hcn : c ≤ n) :
    ∃ (u : Site 2) (cyc : (faceBoundaryGraph (bcd_leftReach ω n)).Walk u u), cyc.IsCycle :=
  jex_exists_dualCircuit ω hn hnoH hc0 hcn






theorem rdv_face_dualCircuit (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
    ∃ (u : Site 2) (c : (faceBoundaryGraph (bcd_leftReach ω n)).Walk u u), c.IsCycle :=
  fdd_leftReach_dualCircuit ω n hn hnoH





theorem rdv_faceOpenDual_cycle (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
    ∃ (u : Site 2) (c : (faceBoundaryGraph (bcd_leftReach ω n)).Walk u u), c.IsCycle :=
  fci_leftReach_faceOpenDual_cycle ω n hn hnoH





theorem rdv_face_dualCircuit_edge_dual_open (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    {f g : Site 2} (hadj : (faceBoundaryGraph (bcd_leftReach ω n)).Adj f g)
    {p q : Site 2} (hpq : sharedPrimalEdge f g = s(p, q))
    (hpadj : (hypercubicLattice 2).Adj p q)
    (hpbox : p ∈ rect 0 n 0 n) (hqbox : q ∈ rect 0 n 0 n) :
    dualConfig ω (crossEdge s(p, q)) = true :=
  jex_dualCircuit_edge_dual_open ω n hadj hpq hpadj hpbox hqbox




theorem rdv_face_contour_nonempty (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
    ∃ f g : Site 2, (faceBoundaryGraph (bcd_leftReach ω n)).Adj f g :=
  fdd_leftReach_faceBoundary_nonempty ω n hn hnoH



















def rdv_FrameReconcile (Φ : Site 2 → Site 2) : Prop :=
  ∀ (f g : Site 2), (hypercubicLattice 2).Adj f g →
    sharedPrimalEdge f g = s(rot90Inv (Φ f), rot90Inv (Φ g))







theorem rdv_no_frameReconcile : ¬ ∃ Φ : Site 2 → Site 2, rdv_FrameReconcile Φ :=
  fci_no_open_dual_relabel





theorem rdv_no_frameChangeIso : ¬ ∃ Φ : Site 2 → Site 2, fci_FrameCompat Φ :=
  fci_no_frameChangeIso








theorem rdv_residue_strength (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    {v w : Site 2} (hv : v ∈ bcd_leftReach ω n) (hwbox : w ∈ rect 0 n 0 n)
    (hadj : (hypercubicLattice 2).Adj v w) (hw : w ∉ bcd_leftReach ω n) :
    (openSubgraph 2 (dualConfig ω)).Adj (rot90Fun v) (rot90Fun w) :=
  fdd_leftReach_barrierEdge_dualAdj ω n hv hwbox hadj hw











theorem rdv_face_frame_dichotomy (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (hn : 0 ≤ n)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
    (bcd_leftReach ω n).Finite ∧
      (∀ {v w : Site 2}, v ∈ bcd_leftReach ω n → w ∈ rect 0 n 0 n →
        (hypercubicLattice 2).Adj v w → w ∉ bcd_leftReach ω n →
        (openSubgraph 2 (dualConfig ω)).Adj (rot90Fun v) (rot90Fun w)) ∧
      (∃ f g : Site 2, (faceBoundaryGraph (bcd_leftReach ω n)).Adj f g) ∧
      (∃ (u : Site 2) (c : (faceBoundaryGraph (bcd_leftReach ω n)).Walk u u),
        c.IsCycle ∧ (fci_faceWalk_to_dualWalk (bcd_leftReach ω n) c).IsCycle) :=
  fci_square_dichotomy ω n hn hnoH







theorem rdv_both_targets_false_on_witness :
    ¬ HorizontalCrossing bcc_wallCfg 0 2 0 2 ∧
      ¬ jex_DualBarrierVCrossing bcc_wallCfg 2 ∧
      ¬ dcp_DualCutConnectsRot bcc_wallCfg 2 :=
  ⟨bcc_noH_wall, bcc_noV_wall, rdv_rotResidue_false_on_noH⟩




theorem rdv_witness_separates {x y : Site 2}
    (hx : x ∈ leftSide 0 2 0 2) (hy : y ∈ rightSide 0 2 0 2) :
    ¬ (latticeMinusBarrier (bcd_leftReach bcc_wallCfg 2)).Reachable x y :=
  jex_leftReach_separates bcc_wallCfg 2 bcc_noH_wall hx hy

end Universality

end StatMech
