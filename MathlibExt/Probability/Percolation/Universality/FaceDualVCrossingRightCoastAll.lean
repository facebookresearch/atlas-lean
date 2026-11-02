/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Percolation.Universality.FaceDualVCrossingRightCoast

/-!
# Connectedness of the right complement and of the right coast

Two complements to `FaceDualVCrossingRightCoast`.

* The right complement `bac_rightComplement ω n` is connected inside `[0, n]² \ L`
  (`L = bcd_leftReach ω n`): without a horizontal crossing the whole right side lies outside `L`,
  so every right-complement vertex reaches `(n, 0)` along the right side
  (`rcm_rightComplement_connected_pair`).
* The hypothesis `bac_RCoastConnected` (every right-coast face reaches the row-`0` frontier face)
  is equivalent, under `¬ HorizontalCrossing ω 0 n 0 n` and `0 ≤ n`, to the symmetric form
  `rcm_RCoastConnectedAll` (any two right-coast faces are joined in the box face barrier). Neither
  is proved for general `ω`.

## Main definitions

* `rcm_RCoastConnectedAll ω n`: any two right-coast faces are joined in the box face barrier.

## Main results

* `rcm_rightComplement_connected_pair`: any two right-complement vertices are joined inside
  `[0, n]² \ L`.
* `rcm_rCoastConnected_of_all`, `rcm_all_of_rCoastConnected`: equivalence with
  `bac_RCoastConnected`.
* `rcm_faceDualVCrossing_of_all`: no horizontal crossing of `[0, n]²` together with
  `rcm_RCoastConnectedAll ω n` gives a face-dual vertical crossing `pmd_FaceDualVCrossing ω n`.
* `rcm_wall_RCoastConnectedAll`: the hypothesis holds on the wall configuration.
-/

@[expose] public section

open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box

namespace StatMech

namespace Universality

/-- A boundary edge `(x, y)–(x + 1, y)` of the left cluster inside the box joins the faces
`![x, y]` and `![x, y - 1]` in the box face barrier. -/
theorem rcm_horizEdge_faces_pmdAdj (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {x y : ℤ}
    (hbd : bdEdge (bcd_leftReach ω n) s(![x, y], ![x + 1, y]))
    (hp : (![x, y] : Site 2) ∈ rect 0 n 0 n) (hq : (![x + 1, y] : Site 2) ∈ rect 0 n 0 n) :
    (pmd_boxFaceBarrier ω n).Adj ![x, y] ![x, y - 1] := by
  rw [pmd_boxFaceBarrier_adj]
  refine ⟨by simp [hypercubicLattice_adj, Fin.sum_univ_two], ![x, y], ![x + 1, y], ?_, hbd, hp, hq⟩
  rw [sharedPrimalEdge_bottom]; unfold faceCorner00 faceCorner10; rfl

/-- A boundary edge `(x, y)–(x, y + 1)` of the left cluster inside the box joins the faces
`![x, y]` and `![x - 1, y]` in the box face barrier. -/
theorem rcm_vertEdge_faces_pmdAdj (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {x y : ℤ}
    (hbd : bdEdge (bcd_leftReach ω n) s(![x, y], ![x, y + 1]))
    (hp : (![x, y] : Site 2) ∈ rect 0 n 0 n) (hq : (![x, y + 1] : Site 2) ∈ rect 0 n 0 n) :
    (pmd_boxFaceBarrier ω n).Adj ![x, y] ![x - 1, y] := by
  rw [pmd_boxFaceBarrier_adj]
  refine ⟨by simp [hypercubicLattice_adj, Fin.sum_univ_two], ![x, y], ![x, y + 1], ?_, hbd, hp, hq⟩
  rw [sharedPrimalEdge_left]; unfold faceCorner00 faceCorner01; rfl

/-- An edge from the left cluster to the right complement is a boundary edge of the left
cluster. -/
theorem rcm_LR_edge_bdEdge (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {p q : Site 2}
    (hpL : p ∈ bcd_leftReach ω n) (hqR : q ∈ bac_rightComplement ω n) :
    bdEdge (bcd_leftReach ω n) s(p, q) := by
  rw [bdEdge_mk]
  have hqnotL : q ∉ bcd_leftReach ω n := (bac_rightComplement_subset_boxMinusL ω n hqR).2
  exact ⟨fun _ => hqnotL, fun _ => hpL⟩

/-- A horizontal edge from the left cluster to the right complement joins the faces above and
below it in the box face barrier. -/
theorem rcm_LR_horizEdge_faces_pmdAdj (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {x y : ℤ}
    (hpL : (![x, y] : Site 2) ∈ bcd_leftReach ω n)
    (hqR : (![x + 1, y] : Site 2) ∈ bac_rightComplement ω n)
    (hp : (![x, y] : Site 2) ∈ rect 0 n 0 n) (hq : (![x + 1, y] : Site 2) ∈ rect 0 n 0 n) :
    (pmd_boxFaceBarrier ω n).Adj ![x, y] ![x, y - 1] :=
  rcm_horizEdge_faces_pmdAdj ω n (rcm_LR_edge_bdEdge ω n hpL hqR) hp hq

/-- Without a horizontal crossing, `(n, 0)` and `(n, t)`, `t ∈ [0, n]`, are joined along the right
side inside `[0, n]² \ L`. -/
theorem rcm_rightWall_reaches_in_boxMinusL (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) {t : ℤ} (ht0 : 0 ≤ t) (htn : t ≤ n) :
    ∃ (h0 : (![n, 0] : Site 2) ∈ bac_boxMinusL ω n)
      (ht : (![n, t] : Site 2) ∈ bac_boxMinusL ω n),
      ((hypercubicLattice 2).induce (bac_boxMinusL ω n)).Reachable ⟨![n, 0], h0⟩ ⟨![n, t], ht⟩ := by
  have hn : 0 ≤ n := le_trans ht0 htn
  have hmem : ∀ s : ℤ, 0 ≤ s → s ≤ n → (![n, s] : Site 2) ∈ bac_boxMinusL ω n := by
    intro s hs0 hsn
    have hR : (![n, s] : Site 2) ∈ rightSide 0 n 0 n := by
      refine ⟨?_, by simp⟩
      rw [mem_rect]; exact ⟨by simp [hn], by simp, by simpa using hs0, by simpa using hsn⟩
    exact ⟨rightSide_subset hR, dcw_rightSide_notin_L ω n hnoH hR⟩
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le ht0
  have hseg : ∀ k : ℕ, k ≤ m →
      Function.update (![n, 0] : Site 2) 1 ((![n, 0] : Site 2) 1 + (k : ℤ))
        ∈ bac_boxMinusL ω n := by
    intro k hk
    have hval : Function.update (![n, 0] : Site 2) 1 ((![n, 0] : Site 2) 1 + (k : ℤ))
        = ![n, (k : ℤ)] := by funext i; fin_cases i <;> simp [Function.update]
    rw [hval]
    have hk' : (k : ℤ) ≤ (m : ℤ) := by exact_mod_cast hk
    exact hmem (k : ℤ) (by positivity) (by omega)
  have hreach := segment_connectedWithin (d := 2) (bac_boxMinusL ω n) (1 : Fin 2)
    (![n, 0] : Site 2) m hseg
  have e0 : Function.update (![n, 0] : Site 2) 1 ((![n, 0] : Site 2) 1 + ((0 : ℕ) : ℤ))
      = ![n, 0] := by funext i; fin_cases i <;> simp [Function.update]
  have em : Function.update (![n, 0] : Site 2) 1 ((![n, 0] : Site 2) 1 + (m : ℤ))
      = ![n, t] := by
    funext i; fin_cases i
    · simp [Function.update]
    · simp only [Function.update]; simp; omega
  have h0 : (![n, 0] : Site 2) ∈ bac_boxMinusL ω n := hmem 0 le_rfl hn
  have ht : (![n, t] : Site 2) ∈ bac_boxMinusL ω n := hmem t ht0 htn
  refine ⟨h0, ht, ?_⟩
  have hsub0 : (⟨![n, 0], h0⟩ : bac_boxMinusL ω n)
      = ⟨Function.update (![n, 0] : Site 2) 1 ((![n, 0] : Site 2) 1 + ((0 : ℕ) : ℤ)),
          hseg 0 (Nat.zero_le m)⟩ := Subtype.ext e0.symm
  have hsubm : (⟨![n, t], ht⟩ : bac_boxMinusL ω n)
      = ⟨Function.update (![n, 0] : Site 2) 1 ((![n, 0] : Site 2) 1 + ((m : ℕ) : ℤ)),
          hseg m le_rfl⟩ := Subtype.ext em.symm
  rw [hsub0, hsubm]; exact hreach

/-- Every right-complement vertex reaches `(n, 0)` inside `[0, n]² \ L`. -/
theorem rcm_rightComplement_reaches_rightWall (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) {v : Site 2} (hv : v ∈ bac_rightComplement ω n) :
    ∃ (hvc : v ∈ bac_boxMinusL ω n) (h0 : (![n, 0] : Site 2) ∈ bac_boxMinusL ω n),
      ((hypercubicLattice 2).induce (bac_boxMinusL ω n)).Reachable ⟨v, hvc⟩ ⟨![n, 0], h0⟩ := by
  obtain ⟨hvc, y, hyR, hyc, hreach⟩ := hv
  obtain ⟨hybox, hy0⟩ := hyR
  rw [mem_rect] at hybox
  obtain ⟨_, _, ht0, htn⟩ := hybox
  have hye : y = ![n, y 1] := by
    funext i; fin_cases i
    · simpa using hy0
    · simp
  obtain ⟨h0, ht, hwall⟩ := rcm_rightWall_reaches_in_boxMinusL ω n hnoH
    (by simpa using ht0) (by simpa using htn)
  have hyc' : (![n, y 1] : Site 2) ∈ bac_boxMinusL ω n := by rw [← hye]; exact hyc
  have hreach' : ((hypercubicLattice 2).induce (bac_boxMinusL ω n)).Reachable ⟨v, hvc⟩
      ⟨![n, y 1], hyc'⟩ := by
    have : (⟨y, hyc⟩ : bac_boxMinusL ω n) = ⟨![n, y 1], hyc'⟩ := Subtype.ext hye
    rwa [this] at hreach
  exact ⟨hvc, h0, hreach'.trans hwall.symm⟩

/-- The right complement is connected inside `[0, n]² \ L`. -/
theorem rcm_rightComplement_connected_pair (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) {u v : Site 2}
    (hu : u ∈ bac_rightComplement ω n) (hv : v ∈ bac_rightComplement ω n) :
    ∃ (huc : u ∈ bac_boxMinusL ω n) (hvc : v ∈ bac_boxMinusL ω n),
      ((hypercubicLattice 2).induce (bac_boxMinusL ω n)).Reachable ⟨u, huc⟩ ⟨v, hvc⟩ := by
  obtain ⟨huc, h0u, hru⟩ := rcm_rightComplement_reaches_rightWall ω n hnoH hu
  obtain ⟨hvc, h0v, hrv⟩ := rcm_rightComplement_reaches_rightWall ω n hnoH hv
  refine ⟨huc, hvc, hru.trans ?_⟩
  have : (⟨![n, 0], h0u⟩ : bac_boxMinusL ω n) = ⟨![n, 0], h0v⟩ := rfl
  rw [this]; exact hrv.symm

/-- Any two right-coast faces are joined in the box face barrier. A hypothesis carrying the planar
content of crossing duality. -/
def rcm_RCoastConnectedAll (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) : Prop :=
  ∀ f g : Site 2, bac_IsRCoastFace ω n f → bac_IsRCoastFace ω n g →
    (pmd_boxFaceBarrier ω n).Reachable f g

/-- `rcm_RCoastConnectedAll` implies `bac_RCoastConnected` (given no horizontal crossing). -/
theorem rcm_rCoastConnected_of_all (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) (hall : rcm_RCoastConnectedAll ω n) :
    bac_RCoastConnected ω n := by
  intro c₀ hc₀ f hf
  obtain ⟨hc0, hcn, _, _⟩ := id hc₀
  have hfront : bac_IsRCoastFace ω n ![c₀, 0] :=
    bac_frontierFace_isRCoast ω n hnoH (le_refl 0) (by omega) hc₀
  exact hall f ![c₀, 0] hf hfront

/-- `bac_RCoastConnected` implies `rcm_RCoastConnectedAll` (given no horizontal crossing). -/
theorem rcm_all_of_rCoastConnected (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    (hres : bac_RCoastConnected ω n) : rcm_RCoastConnectedAll ω n := by
  obtain ⟨c₀, hc₀⟩ := mbc_exists_rightFrontier ω n hn hnoH (le_refl 0) hn
  intro f g hf hg
  exact (hres c₀ hc₀ f hf).trans (hres c₀ hc₀ g hg).symm

/-- `rcm_RCoastConnectedAll` implies the anchor condition `ccc_FrontierReachesBottom`. -/
theorem rcm_reachesBottom_of_all (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    (hall : rcm_RCoastConnectedAll ω n) : ccc_FrontierReachesBottom ω n :=
  bac_reachesBottom_of_rCoastConnected ω n hn hnoH (rcm_rCoastConnected_of_all ω n hnoH hall)

/-- `rcm_RCoastConnectedAll` implies the arc condition `crc2_FrontierArcReaches`. -/
theorem rcm_frontierArcReaches_of_all (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    (hall : rcm_RCoastConnectedAll ω n) : crc2_FrontierArcReaches ω n :=
  bac_frontierArcReaches_of_rCoastConnected ω n hn hnoH (rcm_rCoastConnected_of_all ω n hnoH hall)

/-- Conditional crossing duality: no horizontal crossing of `[0, n]²` together with
`rcm_RCoastConnectedAll ω n` gives a face-dual vertical crossing. -/
theorem rcm_faceDualVCrossing_of_all (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    (hall : rcm_RCoastConnectedAll ω n) : pmd_FaceDualVCrossing ω n :=
  bac_faceDualVCrossing_of_rCoastConnected ω n hn hnoH (rcm_rCoastConnected_of_all ω n hnoH hall)

/-- `rcm_RCoastConnectedAll` holds for the wall configuration. -/
theorem rcm_wall_RCoastConnectedAll : rcm_RCoastConnectedAll bcc_wallCfg 2 :=
  rcm_all_of_rCoastConnected bcc_wallCfg 2 (by norm_num) bcc_noH_wall bac_wall_rCoastConnected

end Universality

end StatMech
