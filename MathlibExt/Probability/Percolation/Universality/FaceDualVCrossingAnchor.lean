/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Percolation.Universality.FaceDualVCrossingFrontier

/-!
# Frontier faces reaching a common anchor

Reformulates the residual hypothesis `mbc_FrontierRungsConnect` of `FaceDualVCrossingFrontier` as a
single anchor condition `ccc_FrontierReachesBottom`: all right-frontier faces `![c, r]`
(`r ∈ [0, n]`) are joined, in the box face barrier `pmd_boxFaceBarrier ω n`, to one common face
`![a₀, b₀]` with `0 ≤ a₀ ≤ n - 1`, `-1 ≤ b₀ ≤ n`. Under `¬ HorizontalCrossing ω 0 n 0 n` and
`0 ≤ n` the two hypotheses are equivalent. Neither is proved for general `ω`.

## Main definitions

* `ccc_FrontierReachesBottom ω n`: every right-frontier face reaches a common anchor face.

## Main results

* `ccc_frontierRungsConnect_of_reachesBottom`, `ccc_reachesAnchor_of_frontierRungsConnect`: the
  equivalence with `mbc_FrontierRungsConnect`.
* `ccc_faceDualVCrossing_of_reachesBottom`: no horizontal crossing of `[0, n]²` together with
  `ccc_FrontierReachesBottom ω n` gives a face-dual vertical crossing `pmd_FaceDualVCrossing ω n`.
* `ccc_wall_frontierReachesBottom`: the anchor condition holds on the wall configuration.
-/

@[expose] public section

open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box

namespace StatMech

namespace Universality

/-- The frontier face `![c, r]` is adjacent in the box face barrier to the face `![c, r - 1]`
below it (they share the frontier edge `(c, r)–(c + 1, r)`). -/
theorem ccc_frontierFace_down_adj (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {c r : ℤ}
    (hr0 : 0 ≤ r) (hrn : r ≤ n) (htr : mbc_IsRightFrontier ω n c r) :
    (pmd_boxFaceBarrier ω n).Adj ![c, r] ![c, r - 1] := by
  obtain ⟨hc0, hcn, hcL, _hmax⟩ := htr
  have hc1 : (![c + 1, r] : Site 2) ∉ bcd_leftReach ω n :=
    mbc_rightFrontier_succ_notMem ω n c r ⟨hc0, hcn, hcL, _hmax⟩
  rw [pmd_boxFaceBarrier_adj]
  refine ⟨by simp [hypercubicLattice_adj, Fin.sum_univ_two], ![c, r], ![c + 1, r], ?_, ?_, ?_, ?_⟩
  · rw [sharedPrimalEdge_bottom]
    unfold faceCorner00 faceCorner10
    rfl
  · rw [bdEdge_mk]; exact ⟨fun _ => hc1, fun _ => hcL⟩
  · rw [mem_rect]
    exact ⟨by simpa using hc0, by simp; omega, by simpa using hr0, by simpa using hrn⟩
  · rw [mem_rect]
    exact ⟨by simp; omega, by simp; omega, by simpa using hr0, by simpa using hrn⟩

/-- The right frontier of a row is unique. -/
theorem ccc_rightFrontier_unique (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {c c' r : ℤ}
    (hc : mbc_IsRightFrontier ω n c r) (hc' : mbc_IsRightFrontier ω n c' r) : c = c' := by
  obtain ⟨hc0, hcn, hcL, hcmax⟩ := hc
  obtain ⟨hc0', hcn', hcL', hcmax'⟩ := hc'
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact hcmax c' h (by omega) hcL'
  · exact hcmax' c h (by omega) hcL

/-- Anchor condition: there is a face `![a₀, b₀]`, `0 ≤ a₀ ≤ n - 1`, `-1 ≤ b₀ ≤ n`, reached in
the box face barrier from every right-frontier face `![c, r]`, `r ∈ [0, n]`. A hypothesis carrying
the planar content of crossing duality; equivalent to `mbc_FrontierRungsConnect` when
`¬ HorizontalCrossing ω 0 n 0 n`. -/
def ccc_FrontierReachesBottom (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) : Prop :=
  ∃ (a₀ b₀ : ℤ), 0 ≤ a₀ ∧ a₀ ≤ n - 1 ∧ -1 ≤ b₀ ∧ b₀ ≤ n ∧
    ∀ (r : ℤ), 0 ≤ r → r ≤ n → ∀ (c : ℤ), mbc_IsRightFrontier ω n c r →
      (pmd_boxFaceBarrier ω n).Reachable ![c, r] ![a₀, b₀]

/-- The anchor condition implies `mbc_FrontierRungsConnect`. -/
theorem ccc_frontierRungsConnect_of_reachesBottom (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hatom : ccc_FrontierReachesBottom ω n) : mbc_FrontierRungsConnect ω n := by
  obtain ⟨a₀, b₀, _ha0, _ha0', _hb0, _hb0', hanchor⟩ := hatom
  intro r hr0 hrn1 c c' hc hc'
  have hrn : r ≤ n := by omega
  have hr1_0 : (0 : ℤ) ≤ r + 1 := by omega
  have hr1_n : r + 1 ≤ n := by omega
  have hreachA : (pmd_boxFaceBarrier ω n).Reachable ![c, r] ![a₀, b₀] := hanchor r hr0 hrn c hc
  have hreachB : (pmd_boxFaceBarrier ω n).Reachable ![c', r + 1] ![a₀, b₀] :=
    hanchor (r + 1) hr1_0 hr1_n c' hc'
  have hrung : (pmd_boxFaceBarrier ω n).Adj ![c', (r + 1) - 1] ![c', r + 1] :=
    mbc_rung_vAdj ω n hr1_0 hr1_n hc'
  have hrung' : (pmd_boxFaceBarrier ω n).Adj ![c', r] ![c', r + 1] := by
    have he : (r + 1) - 1 = r := by ring
    rwa [he] at hrung
  have hreachB' : (pmd_boxFaceBarrier ω n).Reachable ![c', r] ![a₀, b₀] :=
    (hrung'.reachable).trans hreachB
  exact hreachA.trans hreachB'.symm

/-- Conversely, without a horizontal crossing `mbc_FrontierRungsConnect` implies the anchor
condition, with anchor the row-`0` frontier face. -/
theorem ccc_reachesAnchor_of_frontierRungsConnect (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    (hres : mbc_FrontierRungsConnect ω n) : ccc_FrontierReachesBottom ω n := by
  obtain ⟨c₀, hc₀⟩ := mbc_exists_rightFrontier ω n hn hnoH (le_refl 0) hn
  refine ⟨c₀, 0, hc₀.1, hc₀.2.1, by norm_num, hn, ?_⟩
  intro r hr0 hrn c hc
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hr0
  have key : ∀ (k : ℕ), (k : ℤ) ≤ n → ∀ (ck : ℤ), mbc_IsRightFrontier ω n ck (k : ℤ) →
      (pmd_boxFaceBarrier ω n).Reachable ![c₀, (0 : ℤ)] ![ck, (k : ℤ)] := by
    intro k
    induction k with
    | zero =>
      intro _ ck hck
      have : ck = c₀ := ccc_rightFrontier_unique ω n hck hc₀
      subst this; exact Reachable.refl _
    | succ p ih =>
      intro hk ck hck
      have hp_n : (p : ℤ) ≤ n := by push_cast at hk ⊢; omega
      have hp_n1 : (p : ℤ) ≤ n - 1 := by push_cast at hk; omega
      obtain ⟨cp, hcp⟩ := mbc_exists_rightFrontier ω n hn hnoH (by positivity) hp_n
      have hih : (pmd_boxFaceBarrier ω n).Reachable ![c₀, (0 : ℤ)] ![cp, (p : ℤ)] :=
        ih hp_n cp hcp
      have hconn : (pmd_boxFaceBarrier ω n).Reachable ![cp, (p : ℤ)] ![ck, (p : ℤ)] := by
        have hck' : mbc_IsRightFrontier ω n ck ((p : ℤ) + 1) := by
          have hc : (((p : ℕ) + 1 : ℕ) : ℤ) = (p : ℤ) + 1 := by push_cast; ring
          rw [← hc]; exact hck
        exact hres (p : ℤ) (by positivity) hp_n1 cp ck hcp hck'
      have hrung : (pmd_boxFaceBarrier ω n).Adj ![ck, ((p : ℤ) + 1) - 1] ![ck, (p : ℤ) + 1] := by
        have hck' : mbc_IsRightFrontier ω n ck ((p : ℤ) + 1) := by
          have hc : (((p : ℕ) + 1 : ℕ) : ℤ) = (p : ℤ) + 1 := by push_cast; ring
          rw [← hc]; exact hck
        exact mbc_rung_vAdj ω n (by positivity) (by push_cast at hk; omega) hck'
      have hrung' : (pmd_boxFaceBarrier ω n).Adj ![ck, (p : ℤ)] ![ck, (p : ℤ) + 1] := by
        have he : ((p : ℤ) + 1) - 1 = (p : ℤ) := by ring
        rwa [he] at hrung
      have hcast : (((p : ℕ) + 1 : ℕ) : ℤ) = (p : ℤ) + 1 := by push_cast; ring
      rw [hcast]
      exact ((hih.trans hconn).trans hrung'.reachable)
  exact (key m hrn c hc).symm

/-- The anchor condition implies the residual hypothesis `pmd_BarrierConnectsRows` (given no
horizontal crossing). -/
theorem ccc_barrierConnectsRows_of_reachesBottom (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    (hatom : ccc_FrontierReachesBottom ω n) : pmd_BarrierConnectsRows ω n :=
  mbc_barrierConnectsRows_of_residue ω n hn hnoH
    (ccc_frontierRungsConnect_of_reachesBottom ω n hatom)

/-- Conditional crossing duality: no horizontal crossing of `[0, n]²` together with the anchor
condition gives a face-dual vertical crossing. -/
theorem ccc_faceDualVCrossing_of_reachesBottom (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    (hatom : ccc_FrontierReachesBottom ω n) : pmd_FaceDualVCrossing ω n :=
  mbc_faceDualVCrossing_of_residue ω n hn hnoH
    (ccc_frontierRungsConnect_of_reachesBottom ω n hatom)

/-- Dichotomy form of `ccc_faceDualVCrossing_of_reachesBottom` (the right disjunct always holds
under the hypotheses). -/
theorem ccc_exhaustivity_of_reachesBottom (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    (hatom : ccc_FrontierReachesBottom ω n) :
    HorizontalCrossing ω 0 n 0 n ∨ pmd_FaceDualVCrossing ω n :=
  Or.inr (ccc_faceDualVCrossing_of_reachesBottom ω n hn hnoH hatom)

/-- In the wall configuration the face `![0, 0]` is barrier-adjacent to the face `![0, -1]`. -/
theorem ccc_wall_bottom_rung :
    (pmd_boxFaceBarrier bcc_wallCfg 2).Adj ![0, (0 : ℤ)] ![0, (0 : ℤ) - 1] :=
  ccc_frontierFace_down_adj bcc_wallCfg 2 (le_refl 0) (by norm_num)
    (mbc_wall_rightFrontier_at (le_refl 0) (by norm_num))

/-- The anchor condition holds for the wall configuration, with anchor `![0, -1]`. -/
theorem ccc_wall_frontierReachesBottom : ccc_FrontierReachesBottom bcc_wallCfg 2 := by
  refine ⟨0, -1, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  intro r hr0 hrn c hc
  have hc0 : c = 0 := mbc_wall_rightFrontier_zero hc
  subst hc0
  have step : ∀ s : ℤ, 0 ≤ s → s ≤ 2 →
      (pmd_boxFaceBarrier bcc_wallCfg 2).Adj ![0, s - 1] ![0, s] :=
    fun s hs0 hs2 =>
      mbc_rung_vAdj bcc_wallCfg 2 hs0 hs2 (mbc_wall_rightFrontier_at hs0 hs2)
  have hbot : (pmd_boxFaceBarrier bcc_wallCfg 2).Reachable ![0, (0 : ℤ)] ![0, (-1 : ℤ)] := by
    have h := ccc_wall_bottom_rung
    have he : ((0 : ℤ) - 1) = (-1 : ℤ) := by ring
    rw [he] at h
    exact h.reachable
  have h1 : (pmd_boxFaceBarrier bcc_wallCfg 2).Adj ![0, (0 : ℤ)] ![0, (1 : ℤ)] := by
    have h := step 1 (by norm_num) (by norm_num)
    have he : ((1 : ℤ) - 1) = (0 : ℤ) := by ring
    rw [he] at h; exact h
  have h2 : (pmd_boxFaceBarrier bcc_wallCfg 2).Adj ![0, (1 : ℤ)] ![0, (2 : ℤ)] := by
    have h := step 2 (by norm_num) (by norm_num)
    have he : ((2 : ℤ) - 1) = (1 : ℤ) := by ring
    rw [he] at h; exact h
  interval_cases r
  · exact hbot
  · exact (h1.symm.reachable).trans hbot
  · exact ((h2.symm.reachable).trans (h1.symm.reachable)).trans hbot

end Universality

end StatMech
