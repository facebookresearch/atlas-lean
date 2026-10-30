/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Percolation.Universality.FaceDualVCrossingArc

/-!
# The right complement of the left cluster and right-coast faces

Let `L = bcd_leftReach ω n` be the set of vertices of the box `[0, n]²` joined to the left side
by an open path in the box. The *right complement* `bac_rightComplement ω n` is the set of
vertices of `[0, n]² \ L` joined to the right side by a lattice path inside `[0, n]² \ L`.
A *right-coast face* is a face carrying an edge of the box face barrier and having a corner in
the right complement. Right-frontier faces are right-coast faces (`bac_frontierFace_isRCoast`).

The file reduces the anchor condition `ccc_FrontierReachesBottom` to
`bac_RCoastConnected` (every right-coast face reaches the row-`0` frontier face in the box face
barrier), and that in turn to the stronger `bac_BarrierConnected` (all faces carrying a barrier
edge are mutually reachable). Neither is proved for general `ω`. `bac_BarrierConnected` is
strictly stronger than needed and fails in general: when `L` surrounds a hole (a vertex of the box
outside `L` all of whose neighbours lie in `L`), the barrier faces around the hole form a
separate component. It holds on the wall configuration.

## Main definitions

* `bac_boxMinusL ω n`: `[0, n]² \ bcd_leftReach ω n`.
* `bac_rightComplement ω n`: the part of `bac_boxMinusL ω n` connected to the right side inside
  `bac_boxMinusL ω n`.
* `bac_IsRCoastFace`, `bac_RCoastConnected`, `bac_BarrierConnected`: as above.

## Main results

* `bac_gap_mem_rightComplement`: the vertex just right of a row frontier lies in the right
  complement.
* `bac_reachesBottom_of_rCoastConnected`: `bac_RCoastConnected` implies the anchor condition.
* `bac_faceDualVCrossing_of_rCoastConnected`: no horizontal crossing of `[0, n]²` together with
  `bac_RCoastConnected ω n` gives a face-dual vertical crossing `pmd_FaceDualVCrossing ω n`.
* `bac_wall_rCoastConnected`: `bac_RCoastConnected` holds on the wall configuration.
-/

@[expose] public section

open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box

namespace StatMech

namespace Universality

/-- The vertices of the box `[0, n]²` outside the left cluster `bcd_leftReach ω n`. -/
def bac_boxMinusL (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) : Set (Site 2) :=
  rect 0 n 0 n \ bcd_leftReach ω n

/-- The right complement: vertices of `bac_boxMinusL ω n` joined to a vertex of the right side by
a lattice path inside `bac_boxMinusL ω n`. -/
def bac_rightComplement (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) : Set (Site 2) :=
  {v | ∃ (hv : v ∈ bac_boxMinusL ω n) (y : Site 2) (_hy : y ∈ rightSide 0 n 0 n)
        (hyc : y ∈ bac_boxMinusL ω n),
      ((hypercubicLattice 2).induce (bac_boxMinusL ω n)).Reachable ⟨v, hv⟩ ⟨y, hyc⟩}

/-- The right complement lies in the box and outside the left cluster. -/
theorem bac_rightComplement_subset_boxMinusL (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    bac_rightComplement ω n ⊆ bac_boxMinusL ω n := fun _ hv => hv.choose

/-- Without a horizontal crossing every right-side vertex lies in the right complement. -/
theorem bac_rightWall_mem_rightComplement (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) {r : ℤ} (hr0 : 0 ≤ r) (hrn : r ≤ n) :
    (![n, r] : Site 2) ∈ bac_rightComplement ω n := by
  have hn : 0 ≤ n := le_trans hr0 hrn
  have hyR : (![n, r] : Site 2) ∈ rightSide 0 n 0 n := by
    refine ⟨?_, by simp⟩
    rw [mem_rect]; exact ⟨by simp [hn], by simp, by simpa using hr0, by simpa using hrn⟩
  have hyc : (![n, r] : Site 2) ∈ bac_boxMinusL ω n :=
    ⟨rightSide_subset hyR, dcw_rightSide_notin_L ω n hnoH hyR⟩
  exact ⟨hyc, ![n, r], hyR, hyc, SimpleGraph.Reachable.refl _⟩

/-- The vertex `(c + 1, r)` just right of the row-`r` frontier lies in the right complement:
the segment from it to `(n, r)` avoids the left cluster. -/
theorem bac_gap_mem_rightComplement (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (_hnoH : ¬ HorizontalCrossing ω 0 n 0 n) {c r : ℤ}
    (hr0 : 0 ≤ r) (hrn : r ≤ n) (htr : mbc_IsRightFrontier ω n c r) :
    (![c + 1, r] : Site 2) ∈ bac_rightComplement ω n := by
  obtain ⟨hc0, hcn, _hcL, _hmax⟩ := htr
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ n - (c + 1))
  have hseg : ∀ t : ℕ, t ≤ m →
      Function.update (![c + 1, r] : Site 2) 0 ((![c + 1, r] : Site 2) 0 + (t : ℤ))
        ∈ bac_boxMinusL ω n := by
    intro t ht
    have hval : Function.update (![c + 1, r] : Site 2) 0 ((![c + 1, r] : Site 2) 0 + (t : ℤ))
        = ![c + 1 + (t : ℤ), r] := by
      funext i; fin_cases i <;> simp [Function.update]
    rw [hval]
    have ht' : (t : ℤ) ≤ (m : ℤ) := by exact_mod_cast ht
    refine ⟨?_, ?_⟩
    · rw [mem_rect]
      refine ⟨by simp; omega, by simp; omega, by simpa using hr0, by simpa using hrn⟩
    · exact _hmax _ (by omega) (by omega)
  have hreach := segment_connectedWithin (d := 2) (bac_boxMinusL ω n) (0 : Fin 2)
    (![c + 1, r] : Site 2) m hseg
  have e0 : Function.update (![c + 1, r] : Site 2) 0 ((![c + 1, r] : Site 2) 0 + ((0 : ℕ) : ℤ))
      = ![c + 1, r] := by funext i; fin_cases i <;> simp [Function.update]
  have em : Function.update (![c + 1, r] : Site 2) 0 ((![c + 1, r] : Site 2) 0 + (m : ℤ))
      = ![n, r] := by
    funext i
    fin_cases i
    · simp only [Function.update]; simp; omega
    · simp [Function.update]
  have hgapc : (![c + 1, r] : Site 2) ∈ bac_boxMinusL ω n := by
    have := hseg 0 (Nat.zero_le m); rwa [e0] at this
  have hnc : (![n, r] : Site 2) ∈ bac_boxMinusL ω n := by
    have := hseg m le_rfl; rwa [em] at this
  have hn : 0 ≤ n := le_trans hr0 hrn
  have hyR : (![n, r] : Site 2) ∈ rightSide 0 n 0 n := by
    refine ⟨?_, by simp⟩
    rw [mem_rect]; exact ⟨by simp [hn], by simp, by simpa using hr0, by simpa using hrn⟩
  refine ⟨hgapc, ![n, r], hyR, hnc, ?_⟩
  have hsub0 : (⟨![c + 1, r], hgapc⟩ : bac_boxMinusL ω n)
      = ⟨Function.update (![c + 1, r] : Site 2) 0 ((![c + 1, r] : Site 2) 0 + ((0 : ℕ) : ℤ)),
          hseg 0 (Nat.zero_le m)⟩ := Subtype.ext e0.symm
  have hsubm : (⟨![n, r], hnc⟩ : bac_boxMinusL ω n)
      = ⟨Function.update (![c + 1, r] : Site 2) 0 ((![c + 1, r] : Site 2) 0 + ((m : ℕ) : ℤ)),
          hseg m le_rfl⟩ := Subtype.ext em.symm
  rw [hsub0, hsubm]
  exact hreach

/-- Right-coast face: `f` has an edge of the box face barrier and one of its four corners lies in
the right complement. -/
def bac_IsRCoastFace (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (f : Site 2) : Prop :=
  (∃ g : Site 2, (pmd_boxFaceBarrier ω n).Adj f g) ∧
    (∃ p : Site 2, p ∈ bac_rightComplement ω n ∧
      (p = ![f 0, f 1] ∨ p = ![f 0 + 1, f 1] ∨ p = ![f 0, f 1 + 1] ∨ p = ![f 0 + 1, f 1 + 1]))

/-- Right-frontier faces are right-coast faces. -/
theorem bac_frontierFace_isRCoast (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) {c r : ℤ}
    (hr0 : 0 ≤ r) (hrn : r ≤ n) (htr : mbc_IsRightFrontier ω n c r) :
    bac_IsRCoastFace ω n ![c, r] := by
  refine ⟨⟨![c, r - 1], ccc_frontierFace_down_adj ω n hr0 hrn htr⟩, ![c + 1, r], ?_, ?_⟩
  · exact bac_gap_mem_rightComplement ω n hnoH hr0 hrn htr
  · right; left; funext i; fin_cases i <;> simp

/-- Every right-coast face reaches the row-`0` frontier face `![c₀, 0]` in the box face barrier.
A hypothesis carrying the planar content of crossing duality. -/
def bac_RCoastConnected (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) : Prop :=
  ∀ (c₀ : ℤ), mbc_IsRightFrontier ω n c₀ 0 →
    ∀ f : Site 2, bac_IsRCoastFace ω n f →
      (pmd_boxFaceBarrier ω n).Reachable f ![c₀, 0]

/-- `bac_RCoastConnected` implies the anchor condition `ccc_FrontierReachesBottom`. -/
theorem bac_reachesBottom_of_rCoastConnected (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    (hres : bac_RCoastConnected ω n) : ccc_FrontierReachesBottom ω n := by
  obtain ⟨c₀, hc₀⟩ := mbc_exists_rightFrontier ω n hn hnoH (le_refl 0) hn
  obtain ⟨hc0, hcn, _, _⟩ := id hc₀
  refine cac_frontierReachesBottom_of_anchor ω n hc0 hcn (le_refl _) (by omega : (-1 : ℤ) ≤ n) ?_
  intro r hr0 hrn c hc
  have hreach0 : (pmd_boxFaceBarrier ω n).Reachable ![c, r] ![c₀, 0] :=
    hres c₀ hc₀ ![c, r] (bac_frontierFace_isRCoast ω n hnoH hr0 hrn hc)
  exact hreach0.trans (cac_row0_frontier_reaches_bottom ω n hn hc₀)

/-- `bac_RCoastConnected` implies the arc condition `crc2_FrontierArcReaches` (given no horizontal
crossing). -/
theorem bac_frontierArcReaches_of_rCoastConnected (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    (hres : bac_RCoastConnected ω n) : crc2_FrontierArcReaches ω n :=
  crc2_arc_of_atom ω n hn (bac_reachesBottom_of_rCoastConnected ω n hn hnoH hres)

/-- All faces carrying an edge of the box face barrier are mutually reachable in it. Stronger than
`bac_RCoastConnected` and false in general (a hole of the left cluster gives a separate barrier
component). -/
def bac_BarrierConnected (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) : Prop :=
  ∀ f g : Site 2, (∃ f' : Site 2, (pmd_boxFaceBarrier ω n).Adj f f') →
    (∃ g' : Site 2, (pmd_boxFaceBarrier ω n).Adj g g') →
      (pmd_boxFaceBarrier ω n).Reachable f g

/-- `bac_BarrierConnected` implies `bac_RCoastConnected`. -/
theorem bac_rCoastConnected_of_barrierConnected (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (_hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    (h : bac_BarrierConnected ω n) : bac_RCoastConnected ω n := by
  intro c₀ hc₀ f hf
  have hfront : ∃ g' : Site 2, (pmd_boxFaceBarrier ω n).Adj ![c₀, 0] g' :=
    ⟨![c₀, (0 : ℤ) - 1], ccc_frontierFace_down_adj ω n (le_refl 0) hn hc₀⟩
  exact h f ![c₀, 0] hf.1 hfront

/-- Conditional crossing duality: no horizontal crossing of `[0, n]²` together with
`bac_RCoastConnected ω n` gives a face-dual vertical crossing. -/
theorem bac_faceDualVCrossing_of_rCoastConnected (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    (hres : bac_RCoastConnected ω n) : pmd_FaceDualVCrossing ω n :=
  ccc_faceDualVCrossing_of_reachesBottom ω n hn hnoH
    (bac_reachesBottom_of_rCoastConnected ω n hn hnoH hres)

/-- Dichotomy form of `bac_faceDualVCrossing_of_rCoastConnected` (the right disjunct always holds
under the hypotheses). -/
theorem bac_exhaustivity_of_rCoastConnected (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    (hres : bac_RCoastConnected ω n) :
    HorizontalCrossing ω 0 n 0 n ∨ pmd_FaceDualVCrossing ω n :=
  Or.inr (bac_faceDualVCrossing_of_rCoastConnected ω n hn hnoH hres)

/-- In the wall configuration the left cluster is column `0` of the box. -/
theorem bac_wall_leftReach_iff {v : Site 2} (hv : v ∈ rect 0 2 0 2) :
    v ∈ bcd_leftReach bcc_wallCfg 2 ↔ v 0 = 0 := by
  constructor
  · exact rdv_leftReach_wall_x0
  · intro h0
    exact dcw_leftSide_in_L bcc_wallCfg 2 ⟨hv, h0⟩

/-- A face sharing the edge `(0, c)–(1, c)` with a neighbour is `![0, c]` or `![0, c - 1]`. -/
theorem bac_wall_face_from_horiz_edge {f g : Site 2} {c : ℤ}
    (hadj : (hypercubicLattice 2).Adj f g)
    (hedge : sharedPrimalEdge f g = s(![0, c], ![1, c])) :
    f 0 = 0 ∧ (f 1 = c ∨ f 1 = c - 1) := by
  classical
  unfold sharedPrimalEdge at hedge
  by_cases h0 : f 0 = g 0
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h0)] at hedge
    rw [Sym2.eq_iff] at hedge
    rcases hedge with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · have hf0 : f 0 = 0 := by have := congrFun e1 0; simpa using this
      have hM : max (f 1) (g 1) = c := by have := congrFun e1 1; simpa using this
      refine ⟨hf0, ?_⟩
      have hadj' := hadj
      rw [hypercubicLattice_adj, Fin.sum_univ_two, h0] at hadj'
      simp only [sub_self, Int.natAbs_zero, zero_add] at hadj'
      have : g 1 = f 1 + 1 ∨ g 1 = f 1 - 1 := by
        rcases Int.natAbs_eq (f 1 - g 1) with he | he <;> omega
      rcases this with hg | hg
      · right; rw [hg, max_eq_right (by omega : f 1 ≤ f 1 + 1)] at hM; omega
      · left; rw [hg, max_eq_left (by omega : f 1 - 1 ≤ f 1)] at hM; omega
    · have ha : f 0 = 1 := by have := congrFun e1 0; simpa using this
      have hb : f 0 + 1 = 0 := by have := congrFun e2 0; simpa using this
      omega
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h0)] at hedge
    rw [Sym2.eq_iff] at hedge
    exfalso
    rcases hedge with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · have h1 : f 1 = c := by have := congrFun e1 1; simpa using this
      have h2 : f 1 + 1 = c := by have := congrFun e2 1; simpa using this
      omega
    · have h1 : f 1 = c := by have := congrFun e1 1; simpa using this
      have h2 : f 1 + 1 = c := by have := congrFun e2 1; simpa using this
      omega

/-- In the wall configuration every face carrying a barrier edge is `![0, b]` with
`b ∈ {-1, 0, 1, 2}`. -/
theorem bac_wall_barrierFace_col0 {f g : Site 2}
    (h : (pmd_boxFaceBarrier bcc_wallCfg 2).Adj f g) :
    f 0 = 0 ∧ (f 1 = -1 ∨ f 1 = 0 ∨ f 1 = 1 ∨ f 1 = 2) := by
  obtain ⟨hadj, p, q, hpq, hbd, hp, hq⟩ := h
  have hpadj : (hypercubicLattice 2).Adj p q := by
    obtain ⟨p', q', hpq', hadj'⟩ := sharedPrimalEdge_isLatticeEdge hadj
    rw [hpq'] at hpq; rw [Sym2.eq_iff] at hpq
    rcases hpq with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> subst e1 <;> subst e2
    · exact hadj'
    · exact hadj'.symm
  rw [bdEdge_mk] at hbd
  have hpq_diff := hpadj
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hpq_diff
  rw [mem_rect] at hp hq
  by_cases hpL : p ∈ bcd_leftReach bcc_wallCfg 2
  · have hqL : q ∉ bcd_leftReach bcc_wallCfg 2 := (hbd.mp hpL)
    have hp0 : p 0 = 0 := rdv_leftReach_wall_x0 hpL
    have hq0 : q 0 = 1 := by
      have hqne : q 0 ≠ 0 := by
        intro hq00
        exact hqL ((bac_wall_leftReach_iff (by rw [mem_rect]; exact hq)).mpr hq00)
      by_contra hne
      have hsamecol : p 0 = q 0 ∨ (p 0 - q 0).natAbs = 1 := by
        rcases Int.natAbs_eq (p 0 - q 0) with he | he <;> omega
      omega
    have h1 : p 1 = q 1 := by omega
    refine ⟨?_, ?_⟩
    · set c := p 1 with hc
      have hpe : p = ![0, c] := by funext i; fin_cases i <;> simp [hp0, hc]
      have hqe : q = ![1, c] := by funext i; fin_cases i <;> simp [hq0, ← h1, hc]
      have hedge : sharedPrimalEdge f g = s(![0, c], ![1, c]) := by rw [hpq, hpe, hqe]
      exact bac_wall_face_from_horiz_edge hadj hedge |>.1
    · set c := p 1 with hc
      have hpe : p = ![0, c] := by funext i; fin_cases i <;> simp [hp0, hc]
      have hqe : q = ![1, c] := by funext i; fin_cases i <;> simp [hq0, ← h1, hc]
      have hedge : sharedPrimalEdge f g = s(![0, c], ![1, c]) := by rw [hpq, hpe, hqe]
      have hf := bac_wall_face_from_horiz_edge hadj hedge
      have hb : 0 ≤ c ∧ c ≤ 2 := ⟨hp.2.2.1, hp.2.2.2⟩
      rcases hf.2 with h | h <;> omega
  · have hqL : q ∈ bcd_leftReach bcc_wallCfg 2 := by
      by_contra hqn; exact hpL (hbd.mpr hqn)
    have hq0 : q 0 = 0 := rdv_leftReach_wall_x0 hqL
    have hp0 : p 0 = 1 := by
      have hpne : p 0 ≠ 0 := by
        intro hp00
        exact hpL ((bac_wall_leftReach_iff (by rw [mem_rect]; exact hp)).mpr hp00)
      by_contra hne
      have : p 0 = q 0 ∨ (p 0 - q 0).natAbs = 1 := by
        rcases Int.natAbs_eq (p 0 - q 0) with he | he <;> omega
      omega
    have h1 : p 1 = q 1 := by omega
    set c := p 1 with hc
    have hpe : p = ![1, c] := by funext i; fin_cases i <;> simp [hp0, hc]
    have hqe : q = ![0, c] := by funext i; fin_cases i <;> simp [hq0, ← h1, hc]
    have hedge : sharedPrimalEdge f g = s(![0, c], ![1, c]) := by
      rw [hpq, hpe, hqe, Sym2.eq_swap]
    have hf := bac_wall_face_from_horiz_edge hadj hedge
    have hb : 0 ≤ c ∧ c ≤ 2 := ⟨hp.2.2.1, hp.2.2.2⟩
    exact ⟨hf.1, by rcases hf.2 with h | h <;> omega⟩

/-- In the wall configuration the faces `![0, b]`, `b ∈ {-1, 0, 1, 2}`, reach `![0, 0]` in the
box face barrier. -/
theorem bac_wall_col0_reaches_origin {b : ℤ} (hb : b = -1 ∨ b = 0 ∨ b = 1 ∨ b = 2) :
    (pmd_boxFaceBarrier bcc_wallCfg 2).Reachable ![0, b] ![0, 0] := by
  have a1 : (pmd_boxFaceBarrier bcc_wallCfg 2).Adj ![0, (-1 : ℤ)] ![0, (0 : ℤ)] := by
    have h := pmd_wall_barrierVAdj (b := -1) (by tauto)
    rwa [show ((-1 : ℤ) + 1) = (0 : ℤ) from by ring] at h
  have a2 : (pmd_boxFaceBarrier bcc_wallCfg 2).Adj ![0, (0 : ℤ)] ![0, (1 : ℤ)] := by
    have h := pmd_wall_barrierVAdj (b := 0) (by tauto)
    rwa [show ((0 : ℤ) + 1) = (1 : ℤ) from by ring] at h
  have a3 : (pmd_boxFaceBarrier bcc_wallCfg 2).Adj ![0, (1 : ℤ)] ![0, (2 : ℤ)] := by
    have h := pmd_wall_barrierVAdj (b := 1) (by tauto)
    rwa [show ((1 : ℤ) + 1) = (2 : ℤ) from by ring] at h
  rcases hb with rfl | rfl | rfl | rfl
  · exact a1.reachable
  · exact Reachable.refl _
  · exact a2.symm.reachable
  · exact (a3.symm.reachable).trans a2.symm.reachable

/-- `bac_RCoastConnected` holds for the wall configuration. -/
theorem bac_wall_rCoastConnected : bac_RCoastConnected bcc_wallCfg 2 := by
  intro c₀ hc₀ f hf
  have hc₀0 : c₀ = 0 := mbc_wall_rightFrontier_zero hc₀
  subst hc₀0
  obtain ⟨g, hg⟩ := hf.1
  obtain ⟨hf0, hf1⟩ := bac_wall_barrierFace_col0 hg
  have hfe : f = ![0, f 1] := by funext i; fin_cases i <;> simp [hf0]
  rw [hfe]
  exact bac_wall_col0_reaches_origin (by tauto)

end Universality

end StatMech
