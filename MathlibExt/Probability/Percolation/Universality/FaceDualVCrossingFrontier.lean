/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Percolation.Universality.FaceDualVCrossing

/-!
# Right frontier of the left cluster and the rung reduction

Continues the reduction of `FaceDualVCrossing`: under `¬ HorizontalCrossing ω 0 n 0 n`,
produce the residual hypothesis `pmd_BarrierConnectsRows` (the box face barrier of the left
cluster `bcd_leftReach ω n` joins the row of faces below the box to the row above it).

In each row `r ∈ [0, n]` the left cluster contains `(0, r)` but not `(n, r)`; its rightmost point
`(c, r)` in that row is the *right frontier* (`mbc_IsRightFrontier`). The bottom edge
`(c, r)–(c + 1, r)` of the face `![c, r]` is a boundary edge of the left cluster, so the faces
`![c, r - 1]` and `![c, r]` are adjacent in the box face barrier (a "rung", `mbc_rung_vAdj`).
Climbing rungs from row `0` to row `n` gives a barrier path from the row below the box to the
row above it, provided consecutive frontier faces are joined inside each row; that proviso is the
hypothesis `mbc_FrontierRungsConnect`, which is not proved for general `ω`.

## Main definitions

* `mbc_IsRightFrontier ω n c r`: `(c, r)` is the rightmost left-cluster vertex of row `r`.
* `mbc_FrontierRungsConnect ω n`: for each `r < n`, the frontier faces `![c, r]` (row `r`) and
  `![c', r]` (`c'` the frontier of row `r + 1`) are joined in the box face barrier.

## Main results

* `mbc_exists_rightFrontier`: without a horizontal crossing every row `r ∈ [0, n]` has a right
  frontier `c ∈ [0, n - 1]`.
* `mbc_barrierConnectsRows_of_residue`, `mbc_faceDualVCrossing_of_residue`:
  `¬ HorizontalCrossing ω 0 n 0 n ∧ mbc_FrontierRungsConnect ω n → pmd_FaceDualVCrossing ω n`
  (through `pmd_BarrierConnectsRows`).
* `mbc_wall_frontierRungsConnect`: the hypothesis holds on the wall configuration `bcc_wallCfg`.
-/

@[expose] public section

open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box

namespace StatMech

namespace Universality

/-- `(c, r)` is the right frontier of row `r`: `0 ≤ c ≤ n - 1`, `(c, r)` lies in the left cluster
`bcd_leftReach ω n`, and no `(c', r)` with `c < c' ≤ n` does. -/
def mbc_IsRightFrontier (ω : ConfigSpace (Sym2 (Site 2))) (n c r : ℤ) : Prop :=
  0 ≤ c ∧ c ≤ n - 1 ∧ (![c, r] : Site 2) ∈ bcd_leftReach ω n ∧
    ∀ c' : ℤ, c < c' → c' ≤ n → (![c', r] : Site 2) ∉ bcd_leftReach ω n

/-- The vertex just right of the frontier is not in the left cluster. -/
theorem mbc_rightFrontier_succ_notMem (ω : ConfigSpace (Sym2 (Site 2))) (n c r : ℤ)
    (h : mbc_IsRightFrontier ω n c r) : (![c + 1, r] : Site 2) ∉ bcd_leftReach ω n := by
  obtain ⟨hc0, hcn, _hcL, hmax⟩ := h
  exact hmax (c + 1) (by omega) (by omega)

/-- Without a horizontal crossing every row `r ∈ [0, n]` of the box has a right frontier. -/
theorem mbc_exists_rightFrontier (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (hn : 0 ≤ n)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) {r : ℤ} (hr0 : 0 ≤ r) (hrn : r ≤ n) :
    ∃ c : ℤ, mbc_IsRightFrontier ω n c r := by
  classical
  have h0L : (![0, r] : Site 2) ∈ bcd_leftReach ω n := by
    apply dcw_leftSide_in_L
    refine ⟨?_, by simp⟩
    rw [mem_rect]; exact ⟨by simp, by simp [hn], by simpa using hr0, by simpa using hrn⟩
  have hnL : (![n, r] : Site 2) ∉ bcd_leftReach ω n := by
    apply dcw_rightSide_notin_L ω n hnoH
    refine ⟨?_, by simp⟩
    rw [mem_rect]; exact ⟨by simp [hn], by simp, by simpa using hr0, by simpa using hrn⟩
  let S : Finset ℤ := (Finset.Icc 0 n).filter (fun c => (![c, r] : Site 2) ∈ bcd_leftReach ω n)
  have h0mem : (0 : ℤ) ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨le_refl 0, hn⟩, h0L⟩
  obtain ⟨c, hcS, hcmax⟩ := S.exists_max_image id ⟨0, h0mem⟩
  simp only [S, Finset.mem_filter, Finset.mem_Icc] at hcS
  obtain ⟨⟨hc0, hcn⟩, hcL⟩ := hcS
  have hcltn : c < n := by
    rcases lt_or_eq_of_le hcn with h | h
    · exact h
    · subst h; exact absurd hcL hnL
  refine ⟨c, hc0, by omega, hcL, ?_⟩
  intro c' hcc' hc'n hc'L
  have hmem : c' ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨by omega, hc'n⟩, hc'L⟩
  have := hcmax c' hmem; simp only [id] at this; omega

/-- Rung: the faces `![c, r - 1]` and `![c, r]` on either side of the frontier edge
`(c, r)–(c + 1, r)` are adjacent in the box face barrier. -/
theorem mbc_rung_vAdj (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {c r : ℤ}
    (hr0 : 0 ≤ r) (hrn : r ≤ n) (htr : mbc_IsRightFrontier ω n c r) :
    (pmd_boxFaceBarrier ω n).Adj ![c, r - 1] ![c, r] := by
  obtain ⟨hc0, hcn, hcL, _hmax⟩ := htr
  have hc1 : (![c + 1, r] : Site 2) ∉ bcd_leftReach ω n :=
    mbc_rightFrontier_succ_notMem ω n c r ⟨hc0, hcn, hcL, _hmax⟩
  have hface : (![c, r] : Site 2) = ![c, (r - 1) + 1] := by funext i; fin_cases i <;> simp
  rw [pmd_boxFaceBarrier_adj]
  refine ⟨by simp [hypercubicLattice_adj, Fin.sum_univ_two], ![c, r], ![c + 1, r], ?_, ?_, ?_, ?_⟩
  · rw [hface, sharedPrimalEdge_top]
    unfold faceCorner01 faceCorner11
    have hrr : (r - 1) + 1 = r := by ring
    rw [hrr]
  · rw [bdEdge_mk]; exact ⟨fun _ hcontra => hc1 hcontra, fun _ => hcL⟩
  · rw [mem_rect]
    exact ⟨by simpa using hc0, by simp; omega, by simpa using hr0, by simpa using hrn⟩
  · rw [mem_rect]
    exact ⟨by simp; omega, by simp; omega, by simpa using hr0, by simpa using hrn⟩

/-- For every `r ∈ [0, n - 1]`, the frontier face `![c, r]` of row `r` and the face `![c', r]`
below the frontier edge of row `r + 1` are joined in the box face barrier. This is a hypothesis
carrying the planar (Jordan-type) content of the crossing-duality lemma. -/
def mbc_FrontierRungsConnect (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) : Prop :=
  ∀ (r : ℤ), 0 ≤ r → r ≤ n - 1 → ∀ (c c' : ℤ),
    mbc_IsRightFrontier ω n c r → mbc_IsRightFrontier ω n c' (r + 1) →
      (pmd_boxFaceBarrier ω n).Reachable ![c, r] ![c', r]

/-- Climbing rungs: under `mbc_FrontierRungsConnect`, the face below the row-`0` frontier reaches
the frontier face of every row `k ≤ n` in the box face barrier. -/
theorem mbc_reach_to_row (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (hn : 0 ≤ n)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    (hres : mbc_FrontierRungsConnect ω n)
    {c0 : ℤ} (h0 : mbc_IsRightFrontier ω n c0 0) :
    ∀ (k : ℕ), (k : ℤ) ≤ n →
      ∃ ck : ℤ, mbc_IsRightFrontier ω n ck (k : ℤ) ∧
        (pmd_boxFaceBarrier ω n).Reachable ![c0, -1] ![ck, (k : ℤ)] := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨c0, h0, ?_⟩
    have hrung : (pmd_boxFaceBarrier ω n).Adj ![c0, (0 : ℤ) - 1] ![c0, (0 : ℤ)] :=
      mbc_rung_vAdj ω n (le_refl 0) hn h0
    simpa using hrung.reachable
  | succ m ih =>
    intro hk
    have hm : (m : ℤ) ≤ n := by push_cast at hk ⊢; omega
    obtain ⟨cm, hcm, hreachm⟩ := ih hm
    have hm1_0 : (0 : ℤ) ≤ ((m : ℤ) + 1) := by positivity
    have hm1_n : ((m : ℤ) + 1) ≤ n := by push_cast at hk; omega
    obtain ⟨cm1, hcm1⟩ := mbc_exists_rightFrontier ω n hn hnoH hm1_0 hm1_n
    have hconn : (pmd_boxFaceBarrier ω n).Reachable ![cm, (m : ℤ)] ![cm1, (m : ℤ)] := by
      have hmle : (m : ℤ) ≤ n - 1 := by omega
      exact hres (m : ℤ) (by positivity) hmle cm cm1 hcm hcm1
    have hrung : (pmd_boxFaceBarrier ω n).Adj ![cm1, ((m : ℤ) + 1) - 1] ![cm1, ((m : ℤ) + 1)] :=
      mbc_rung_vAdj ω n hm1_0 hm1_n hcm1
    have hrung' : (pmd_boxFaceBarrier ω n).Adj ![cm1, (m : ℤ)] ![cm1, ((m : ℤ) + 1)] := by
      have he : ((m : ℤ) + 1) - 1 = (m : ℤ) := by ring
      rwa [he] at hrung
    refine ⟨cm1, ?_, ?_⟩
    · have hc : (((m : ℕ) + 1 : ℕ) : ℤ) = (m : ℤ) + 1 := by push_cast; ring
      rw [hc]; exact hcm1
    · have hstep : (pmd_boxFaceBarrier ω n).Reachable ![cm, (m : ℤ)] ![cm1, ((m : ℤ) + 1)] :=
        hconn.trans hrung'.reachable
      have hcast : (((m : ℕ) + 1 : ℕ) : ℤ) = (m : ℤ) + 1 := by push_cast; ring
      rw [hcast]; exact hreachm.trans hstep

/-- `mbc_FrontierRungsConnect` implies the residual hypothesis `pmd_BarrierConnectsRows`. -/
theorem mbc_barrierConnectsRows_of_residue (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (hn : 0 ≤ n)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) (hres : mbc_FrontierRungsConnect ω n) :
    pmd_BarrierConnectsRows ω n := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  obtain ⟨c0, hc0⟩ := mbc_exists_rightFrontier ω (m : ℤ) hn hnoH (le_refl 0) (by positivity)
  obtain ⟨cn, hcn, hreach⟩ := mbc_reach_to_row ω (m : ℤ) hn hnoH hres hc0 m (le_refl _)
  exact ⟨c0, cn, hc0.1, hc0.2.1, hcn.1, hcn.2.1, hreach⟩

/-- Conditional crossing duality: no horizontal crossing of `[0, n]²` together with
`mbc_FrontierRungsConnect ω n` gives a face-dual vertical crossing. -/
theorem mbc_faceDualVCrossing_of_residue (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (hn : 0 ≤ n)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) (hres : mbc_FrontierRungsConnect ω n) :
    pmd_FaceDualVCrossing ω n :=
  pmd_faceDualVCrossing_of_residue ω n (mbc_barrierConnectsRows_of_residue ω n hn hnoH hres)

/-- In the wall configuration every right frontier is in column `0`. -/
theorem mbc_wall_rightFrontier_zero {c r : ℤ} (h : mbc_IsRightFrontier bcc_wallCfg 2 c r) :
    c = 0 := by
  obtain ⟨_hc0, _hcn, hcL, _hmax⟩ := h
  simpa using rdv_leftReach_wall_x0 hcL

/-- `mbc_FrontierRungsConnect` holds for the wall configuration. -/
theorem mbc_wall_frontierRungsConnect : mbc_FrontierRungsConnect bcc_wallCfg 2 := by
  intro r _hr0 _hrn c c' hc hc'
  have e1 : c = 0 := mbc_wall_rightFrontier_zero hc
  have e2 : c' = 0 := mbc_wall_rightFrontier_zero hc'
  subst e1; subst e2
  exact Reachable.refl _

/-- In the wall configuration column `0` is the right frontier of every row `r ∈ [0, 2]`. -/
theorem mbc_wall_rightFrontier_at {r : ℤ} (hr0 : 0 ≤ r) (hr2 : r ≤ 2) :
    mbc_IsRightFrontier bcc_wallCfg 2 0 r := by
  refine ⟨le_refl 0, by norm_num, ?_, ?_⟩
  · apply dcw_leftSide_in_L
    refine ⟨?_, by simp⟩
    rw [mem_rect]; exact ⟨by simp, by norm_num, by simpa using hr0, by simpa using hr2⟩
  · intro c' _hc' hc'2 hc'L
    have := rdv_leftReach_wall_x0 hc'L
    simp at this; omega

end Universality

end StatMech
