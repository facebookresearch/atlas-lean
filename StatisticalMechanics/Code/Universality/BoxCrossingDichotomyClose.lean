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









def bcc_wallCfg : ConfigSpace (Sym2 (Site 2)) := fun e =>
  !(e = s(![0,0],![1,0]) || e = s(![0,1],![1,1]) || e = s(![0,2],![1,2]))


theorem bcc_site_eq_x0 {a : Site 2} (ha0 : a 0 = 0) : a = ![0, a 1] := by
  funext i; fin_cases i
  · simpa using ha0
  · simp


theorem bcc_site_eq_x1 {b : Site 2} (hb0 : b 0 = 1) {c : ℤ} (h1 : b 1 = c) : b = ![1, c] := by
  funext i; fin_cases i
  · simpa using hb0
  · simpa using h1










theorem bcc_is_wall_edge {a b : Site 2} (ha0 : a 0 = 0) (hb0 : b 0 = 1) (h1 : a 1 = b 1)
    (hc : a 1 = 0 ∨ a 1 = 1 ∨ a 1 = 2) :
    s(a, b) = s(![0,0],![1,0]) ∨ s(a, b) = s(![0,1],![1,1]) ∨ s(a, b) = s(![0,2],![1,2]) := by
  have hae : a = ![0, a 1] := bcc_site_eq_x0 ha0
  have hbe : b = ![1, a 1] := bcc_site_eq_x1 hb0 h1.symm
  rcases hc with h | h | h
  · left; rw [hae, hbe, h]
  · right; left; rw [hae, hbe, h]
  · right; right; rw [hae, hbe, h]





theorem bcc_wall_open_keeps_x0 {a b : Site 2} (hab : (hypercubicLattice 2).Adj a b)
    (ha : a ∈ rect 0 2 0 2) (hb : b ∈ rect 0 2 0 2)
    (hopen : bcc_wallCfg s(a, b) = true) : (a 0 = 0 ↔ b 0 = 0) := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hab
  rw [mem_rect] at ha hb
  by_contra hne
  have hx : a 0 ≠ b 0 := by intro h; rw [h] at hne; exact hne Iff.rfl
  have h1 : a 1 = b 1 := by omega
  have hcase : (a 0 = 0 ∧ b 0 = 1) ∨ (a 0 = 1 ∧ b 0 = 0) := by omega
  have heq : s(a,b) = s(![0,0],![1,0]) ∨ s(a,b) = s(![0,1],![1,1]) ∨ s(a,b) = s(![0,2],![1,2]) := by
    rcases hcase with ⟨ha0, hb0⟩ | ⟨ha0, hb0⟩
    · exact bcc_is_wall_edge ha0 hb0 h1 (by omega)
    · rw [Sym2.eq_swap]; exact bcc_is_wall_edge hb0 ha0 h1.symm (by omega)
  rcases heq with h | h | h <;> (rw [h] at hopen; simp [bcc_wallCfg] at hopen)


theorem bcc_wall_walk_keeps_x0 {x y : (rect 0 2 0 2 : Set (Site 2))}
    (w : (openSubgraphInduce 2 bcc_wallCfg (rect 0 2 0 2)).Walk x y) :
    ((x : Site 2) 0 = 0 ↔ (y : Site 2) 0 = 0) := by
  induction w with
  | nil => exact Iff.rfl
  | @cons a b c hab p ih =>
    rw [openSubgraphInduce_adj, openSubgraph_adj] at hab
    exact (bcc_wall_open_keeps_x0 hab.1 a.2 b.2 hab.2).trans ih




theorem bcc_noH_wall : ¬ HorizontalCrossing bcc_wallCfg 0 2 0 2 := by
  rintro ⟨x, y, hxy⟩
  have hinv := bcc_wall_walk_keeps_x0 (x := ⟨(x:Site 2), leftSide_subset x.2⟩)
    (y := ⟨(y:Site 2), rightSide_subset y.2⟩) hxy.some
  have hx0 : (x : Site 2) 0 = 0 := x.2.2
  have hy0 : (y : Site 2) 0 = 2 := y.2.2
  rw [hy0] at hinv
  have : (2:ℤ) = 0 := hinv.mp hx0
  norm_num at this











theorem bcc_wallCfg_false_iff (e : Sym2 (Site 2)) :
    bcc_wallCfg e = false ↔
      (e = s(![0,0],![1,0]) ∨ e = s(![0,1],![1,1]) ∨ e = s(![0,2],![1,2])) := by
  unfold bcc_wallCfg
  rw [Bool.not_eq_false', Bool.or_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    decide_eq_true_eq, decide_eq_true_eq, or_assoc]


theorem bcc_crossEdge_symm_mk (x y : Site 2) :
    crossEdge.symm s(x, y) = s(rot90Inv x, rot90Inv y) := by
  simp [crossEdge, sym2Congr]


theorem bcc_dualOpen_char {p q : Site 2} (h : dualConfig bcc_wallCfg s(p, q) = true) :
    s(rot90Inv p, rot90Inv q) = s(![0,0],![1,0]) ∨
    s(rot90Inv p, rot90Inv q) = s(![0,1],![1,1]) ∨
    s(rot90Inv p, rot90Inv q) = s(![0,2],![1,2]) := by
  rw [dual_isOpen_iff_isClosed, bcc_crossEdge_symm_mk] at h
  exact (bcc_wallCfg_false_iff _).mp h


theorem bcc_rot90Inv_fst (p : Site 2) : (rot90Inv p) 0 = p 1 := by simp [rot90Inv]




theorem bcc_dualOpen_snd_le {p q : Site 2} (h : dualConfig bcc_wallCfg s(p, q) = true) :
    p 1 ≤ 1 ∧ q 1 ≤ 1 := by
  have hc := bcc_dualOpen_char h
  have key : ∀ {r1 r2 : Site 2},
      s(r1, r2) = s(![0,(0:ℤ)],![1,0]) ∨ s(r1,r2) = s(![0,(1:ℤ)],![1,1]) ∨
        s(r1,r2) = s(![0,(2:ℤ)],![1,2]) →
      (r1 0 = 0 ∨ r1 0 = 1) ∧ (r2 0 = 0 ∨ r2 0 = 1) := by
    intro r1 r2 hr
    rcases hr with h | h | h <;>
    · rw [Sym2.eq_iff] at h
      rcases h with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> subst e1 <;> subst e2 <;> refine ⟨by simp, by simp⟩
  obtain ⟨hp, hq⟩ := key hc
  rw [bcc_rot90Inv_fst] at hp hq
  exact ⟨by omega, by omega⟩


theorem bcc_dualVwalk_keeps_snd {x y : (rect 0 2 0 2 : Set (Site 2))}
    (w : (openSubgraphInduce 2 (dualConfig bcc_wallCfg) (rect 0 2 0 2)).Walk x y)
    (hx : (x : Site 2) 1 ≤ 1) : (y : Site 2) 1 ≤ 1 := by
  induction w with
  | nil => exact hx
  | @cons a b c hab p ih =>
    rw [openSubgraphInduce_adj, openSubgraph_adj] at hab
    exact ih (bcc_dualOpen_snd_le hab.2).2




theorem bcc_noV_wall : ¬ DualVerticalCrossing bcc_wallCfg 0 2 0 2 := by
  rintro ⟨x, y, hxy⟩
  have hx1 : (x : Site 2) 1 = 0 := x.2.2
  have hy1 : (y : Site 2) 1 = 2 := y.2.2
  have hinv := bcc_dualVwalk_keeps_snd (x := ⟨(x:Site 2), bottomSide_subset x.2⟩)
    (y := ⟨(y:Site 2), topSide_subset y.2⟩) hxy.some (by rw [hx1]; norm_num)
  rw [hy1] at hinv
  norm_num at hinv





theorem bcc_wall_noH_noV :
    ¬ HorizontalCrossing bcc_wallCfg 0 2 0 2 ∧ ¬ DualVerticalCrossing bcc_wallCfg 0 2 0 2 :=
  ⟨bcc_noH_wall, bcc_noV_wall⟩













theorem bcc_dichotomy_false :
    ¬ ((horizontalCrossingEvent 0 2 0 2)ᶜ ⊆ dualVerticalCrossingEvent 0 2 0 2) := by
  intro hsub
  have hmem : bcc_wallCfg ∈ (horizontalCrossingEvent 0 2 0 2)ᶜ := by
    rw [Set.mem_compl_iff, mem_horizontalCrossingEvent]; exact bcc_noH_wall
  have hdv : bcc_wallCfg ∈ dualVerticalCrossingEvent 0 2 0 2 := hsub hmem
  rw [mem_dualVerticalCrossingEvent] at hdv
  exact bcc_noV_wall hdv










def bcc_botCfg : ConfigSpace (Sym2 (Site 2)) := fun _ => false



theorem bcc_connWithin_bot_eq {S : Set (Site 2)} {x y : S}
    (h : ConnectedWithin 2 bcc_botCfg S x y) : x = y := by
  unfold ConnectedWithin at h
  obtain ⟨w⟩ := h
  cases w with
  | nil => rfl
  | cons hadj p =>
    exfalso
    rw [openSubgraphInduce_adj] at hadj
    simp only [openSubgraph_adj, bcc_botCfg] at hadj
    exact absurd hadj.2 (by decide)


theorem bcc_leftReach_bot_eq (n : ℤ) :
    bcd_leftReach bcc_botCfg n = leftSide 0 n 0 n := by
  ext v
  constructor
  · rintro ⟨hvbox, x, hxL, hvbox', hconn⟩
    have hxv : (⟨x, leftSide_subset hxL⟩ : (rect 0 n 0 n : Set (Site 2))) = ⟨v, hvbox'⟩ :=
      bcc_connWithin_bot_eq hconn
    have hxveq : x = v := congrArg Subtype.val hxv
    rw [← hxveq]; exact hxL
  · intro hv
    refine ⟨leftSide_subset hv, v, hv, leftSide_subset hv, ?_⟩
    exact connectedWithin_refl bcc_botCfg (rect 0 n 0 n) ⟨v, leftSide_subset hv⟩



theorem bcc_barrier_bot_char {v w : Site 2} (h : dcw_isBarrierEdge bcc_botCfg 2 v w) :
    v 0 = 0 ∧ v 1 = w 1 ∧ w 0 = 1 := by
  obtain ⟨hvL, hwbox, hwnL, hadj⟩ := h
  rw [bcc_leftReach_bot_eq] at hvL hwnL
  have hv0 : v 0 = 0 := hvL.2
  rw [mem_rect] at hwbox
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
  have hwL : ¬ (w ∈ rect 0 2 0 2 ∧ w 0 = 0) := by
    simpa [leftSide, mem_rect] using hwnL
  have hw0 : w 0 ≠ 0 := fun hw00 => hwL ⟨by rw [mem_rect]; exact hwbox, hw00⟩
  rw [hv0] at hadj
  refine ⟨hv0, by omega, by omega⟩




theorem bcc_dualBarrier_bot_snd_le {p q : Site 2}
    (h : (dcw_dualBarrierGraph bcc_botCfg 2).Adj p q) : p 1 ≤ 1 ∧ q 1 ≤ 1 := by
  obtain ⟨v, w, hvw, hpq⟩ := h
  obtain ⟨hv0, _hvw1, hw0⟩ := bcc_barrier_bot_char hvw
  have hrv1 : (rot90Fun v) 1 = v 0 := by simp [rot90Fun]
  have hrw1 : (rot90Fun w) 1 = w 0 := by simp [rot90Fun]
  rcases hpq with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · rw [hp, hq, hrv1, hrw1, hv0, hw0]; omega
  · rw [hp, hq, hrw1, hrv1, hv0, hw0]; omega



theorem bcc_barrier_walk_snd_le {p q : Site 2}
    (c : (dcw_dualBarrierGraph bcc_botCfg 2).Walk p q) (hp : p 1 ≤ 1) :
    ∀ z ∈ c.support, z 1 ≤ 1 := by
  induction c with
  | nil =>
    intro z hz
    simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
    subst hz; exact hp
  | @cons a b d hab pw ih =>
    intro z hz
    have hab' := bcc_dualBarrier_bot_snd_le hab
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hp
    · exact ih hab'.2 z hz





theorem bcc_barrierRoute_false : ¬ dcw_BarrierRoute bcc_botCfg 2 := by
  rintro ⟨p₀, hp₀, q₀, hq₀, c, _hsupp⟩
  have hp0 : p₀ 1 = 0 := hp₀.2
  have hq0 : q₀ 1 = 2 := hq₀.2
  have hsnd := bcc_barrier_walk_snd_le c (by rw [hp0]; norm_num) q₀ c.end_mem_support
  rw [hq0] at hsnd
  norm_num at hsnd


theorem bcc_dualConfig_bot (e : Sym2 (Site 2)) : dualConfig bcc_botCfg e = true := by
  simp [dualConfig, bcc_botCfg]




theorem bcc_dualVert_botCfg : DualVerticalCrossing bcc_botCfg 0 2 0 2 := by
  unfold DualVerticalCrossing VerticalCrossing
  have hb : (![0,0] : Site 2) ∈ bottomSide 0 2 0 2 := by
    refine ⟨?_, by simp⟩; rw [mem_rect]; exact ⟨by simp, by simp, by simp, by simp⟩
  have ht : (![0,2] : Site 2) ∈ topSide 0 2 0 2 := by
    refine ⟨?_, by simp⟩; rw [mem_rect]; exact ⟨by simp, by simp, by simp, by simp⟩
  refine ⟨⟨![0,0], hb⟩, ⟨![0,2], ht⟩, ?_⟩
  have a01 : (openSubgraph 2 (dualConfig bcc_botCfg)).Adj ![0,0] ![0,1] := by
    rw [openSubgraph_adj]; refine ⟨?_, bcc_dualConfig_bot _⟩
    rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
  have a12 : (openSubgraph 2 (dualConfig bcc_botCfg)).Adj ![0,1] ![0,2] := by
    rw [openSubgraph_adj]; refine ⟨?_, bcc_dualConfig_bot _⟩
    rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
  set W : (openSubgraph 2 (dualConfig bcc_botCfg)).Walk ![0,0] ![0,2] :=
    a01.toWalk.append a12.toWalk with hW
  have hsupp : ∀ z ∈ W.support, z ∈ rect 0 2 0 2 := by
    intro z hz
    have hl : W.support = [![(0:ℤ),0], ![(0:ℤ),1], ![(0:ℤ),2]] := by rw [hW]; simp
    rw [hl] at hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with h | h | h <;>
      (subst h; rw [mem_rect]; exact ⟨by simp, by simp, by simp, by simp⟩)
  exact walk_induce_reachable (openSubgraph 2 (dualConfig bcc_botCfg)) (rect 0 2 0 2) W hsupp
    (bottomSide_subset hb) (topSide_subset ht)














def bcc_dualBottomReach (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) : Set (Site 2) :=
  {v | v ∈ rect 0 n 0 n ∧ ∃ (x : Site 2) (_hx : x ∈ bottomSide 0 n 0 n) (hv : v ∈ rect 0 n 0 n),
      ConnectedWithin 2 (dualConfig ω) (rect 0 n 0 n) ⟨x, bottomSide_subset _hx⟩ ⟨v, hv⟩}


theorem bcc_dualVert_iff_reach_top (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    DualVerticalCrossing ω 0 n 0 n ↔
      ∃ y : Site 2, y ∈ topSide 0 n 0 n ∧ y ∈ bcc_dualBottomReach ω n := by
  constructor
  · rintro ⟨x, y, hxy⟩
    refine ⟨(y : Site 2), y.2, topSide_subset y.2, (x : Site 2), x.2, topSide_subset y.2, ?_⟩
    exact hxy
  · rintro ⟨y, hyT, _hybox, x, hxB, hyb, hconn⟩
    exact ⟨⟨x, hxB⟩, ⟨y, hyT⟩, hconn⟩


theorem bcc_bottomSide_in_dualReach (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    {x : Site 2} (hx : x ∈ bottomSide 0 n 0 n) : x ∈ bcc_dualBottomReach ω n :=
  ⟨bottomSide_subset hx, x, hx, bottomSide_subset hx,
    connectedWithin_refl (dualConfig ω) (rect 0 n 0 n) ⟨x, bottomSide_subset hx⟩⟩




theorem bcc_dualReach_extend (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {v w : Site 2}
    (hv : v ∈ bcc_dualBottomReach ω n) (hwbox : w ∈ rect 0 n 0 n)
    (hadj : (hypercubicLattice 2).Adj v w) (hopen : dualConfig ω s(v, w) = true) :
    w ∈ bcc_dualBottomReach ω n := by
  obtain ⟨_hvbox, x, hxB, hvbox', hconn⟩ := hv
  refine ⟨hwbox, x, hxB, hwbox, ?_⟩
  have hstep : (openSubgraphInduce 2 (dualConfig ω) (rect 0 n 0 n)).Adj ⟨v, hvbox'⟩ ⟨w, hwbox⟩ := by
    rw [openSubgraphInduce_adj]; exact ⟨hadj, hopen⟩
  exact hconn.trans hstep.reachable




theorem bcc_dualReach_boundary_closed (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    {v w : Site 2} (hv : v ∈ bcc_dualBottomReach ω n) (hwbox : w ∈ rect 0 n 0 n)
    (hadj : (hypercubicLattice 2).Adj v w) (hw : w ∉ bcc_dualBottomReach ω n) :
    dualConfig ω s(v, w) = false := by
  by_contra h
  rw [Bool.not_eq_false] at h
  exact hw (bcc_dualReach_extend ω n hv hwbox hadj h)




theorem bcc_dualReach_boundary_primal_open (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    {v w : Site 2} (hv : v ∈ bcc_dualBottomReach ω n) (hwbox : w ∈ rect 0 n 0 n)
    (hadj : (hypercubicLattice 2).Adj v w) (hw : w ∉ bcc_dualBottomReach ω n) :
    ω (crossEdge.symm s(v, w)) = true := by
  have hcl := bcc_dualReach_boundary_closed ω n hv hwbox hadj hw
  unfold dualConfig at hcl
  simpa using hcl


theorem bcc_topSide_notin_dualReach (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hno : ¬ DualVerticalCrossing ω 0 n 0 n) {y : Site 2} (hy : y ∈ topSide 0 n 0 n) :
    y ∉ bcc_dualBottomReach ω n := by
  intro hyD
  exact hno ((bcc_dualVert_iff_reach_top ω n).mpr ⟨y, hy, hyD⟩)







theorem bcc_dualReach_separates (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hno : ¬ DualVerticalCrossing ω 0 n 0 n)
    {x y : Site 2} (hx : x ∈ bottomSide 0 n 0 n) (hy : y ∈ topSide 0 n 0 n) :
    ¬ (latticeMinusBarrier (bcc_dualBottomReach ω n)).Reachable x y :=
  not_reachable_latticeMinusBarrier (bcc_dualBottomReach ω n)
    (bcc_bottomSide_in_dualReach ω n hx) (bcc_topSide_notin_dualReach ω n hno hy)

end Universality

end StatMech
