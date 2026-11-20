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
import Code.Lattice.JordanZ2
import Code.Lattice.JordanEnclosure
import Code.Lattice.JordanContour
import Code.Lattice.SegmentConn
import Code.Universality.DualEventSetEquality
import Code.Universality.BoxCrossingDichotomy
import Code.Universality.BoxCrossingDichotomyClose
import Code.Universality.JordanExhaustivityClose
import Code.Universality.RSWFrameReconcileClose

open Set SimpleGraph Finset
open StatMech.Lattice
open StatMech.RSW.Box

namespace StatMech

namespace Universality









theorem mpd_rot90Inv_rect (a b c d : ℤ) (x : Site 2) :
    x ∈ rect a b c d ↔ rot90Inv x ∈ rect c d (-b) (-a) := by
  simp only [mem_rect, des_rot90Inv_zero, des_rot90Inv_one]
  constructor <;> intro h <;> exact ⟨by omega, by omega, by omega, by omega⟩



theorem mpd_rot90Inv_bottomSide (a b c d : ℤ) (x : Site 2) :
    x ∈ bottomSide a b c d ↔ rot90Inv x ∈ leftSide c d (-b) (-a) := by
  simp only [mem_bottomSide, mem_leftSide, mem_rect, des_rot90Inv_zero, des_rot90Inv_one]
  constructor <;> rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩ <;>
    exact ⟨⟨by omega, by omega, by omega, by omega⟩, by omega⟩



theorem mpd_rot90Inv_topSide (a b c d : ℤ) (x : Site 2) :
    x ∈ topSide a b c d ↔ rot90Inv x ∈ rightSide c d (-b) (-a) := by
  simp only [mem_topSide, mem_rightSide, mem_rect, des_rot90Inv_zero, des_rot90Inv_one]
  constructor <;> rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩ <;>
    exact ⟨⟨by omega, by omega, by omega, by omega⟩, by omega⟩



noncomputable def mpd_inducedHom (a b c d : ℤ) (ω : ConfigSpace (Sym2 (Site 2))) :
    (openSubgraphInduce 2 (dualConfig ω) (rect a b c d)) →g
      (openSubgraphInduce 2 (des_negConfig ω) (rect c d (-b) (-a))) where
  toFun := fun x => ⟨rot90Inv (x : Site 2), (mpd_rot90Inv_rect a b c d x).1 x.2⟩
  map_rel' := by
    intro x y hxy
    rw [openSubgraphInduce_adj, openSubgraph_adj] at hxy
    change IsOpenEdge 2 (des_negConfig ω) (rot90Inv (x : Site 2)) (rot90Inv (y : Site 2))
    exact (des_isOpenEdge_dual_iff ω (x : Site 2) (y : Site 2)).1 hxy


noncomputable def mpd_inducedHomInv (a b c d : ℤ) (ω : ConfigSpace (Sym2 (Site 2))) :
    (openSubgraphInduce 2 (des_negConfig ω) (rect c d (-b) (-a))) →g
      (openSubgraphInduce 2 (dualConfig ω) (rect a b c d)) where
  toFun := fun x => ⟨rot90Fun (x : Site 2),
    (mpd_rot90Inv_rect a b c d (rot90Fun (x : Site 2))).2 (by
      rw [show rot90Inv (rot90Fun (x : Site 2)) = (x : Site 2) from
        rot90Equiv.left_inv (x : Site 2)]; exact x.2)⟩
  map_rel' := by
    intro x y hxy
    rw [openSubgraphInduce_adj, openSubgraph_adj] at hxy
    change IsOpenEdge 2 (dualConfig ω) (rot90Fun (x : Site 2)) (rot90Fun (y : Site 2))
    rw [des_isOpenEdge_dual_iff ω (rot90Fun (x : Site 2)) (rot90Fun (y : Site 2))]
    rw [show rot90Inv (rot90Fun (x : Site 2)) = (x : Site 2) from rot90Equiv.left_inv (x : Site 2),
       show rot90Inv (rot90Fun (y : Site 2)) = (y : Site 2) from rot90Equiv.left_inv (y : Site 2)]
    exact hxy





theorem mpd_dualV_iff_negH (ω : ConfigSpace (Sym2 (Site 2))) (a b c d : ℤ) :
    DualVerticalCrossing ω a b c d ↔ HorizontalCrossing (des_negConfig ω) c d (-b) (-a) := by
  constructor
  · rintro ⟨x, y, hxy⟩
    refine ⟨⟨rot90Inv (x : Site 2), (mpd_rot90Inv_bottomSide a b c d x).1 x.2⟩,
            ⟨rot90Inv (y : Site 2), (mpd_rot90Inv_topSide a b c d y).1 y.2⟩, ?_⟩
    exact (hxy : (openSubgraphInduce 2 (dualConfig ω) (rect a b c d)).Reachable _ _).map
      (mpd_inducedHom a b c d ω)
  · rintro ⟨x, y, hxy⟩
    refine ⟨⟨rot90Fun (x : Site 2), ?_⟩, ⟨rot90Fun (y : Site 2), ?_⟩, ?_⟩
    · rw [mpd_rot90Inv_bottomSide a b c d, show rot90Inv (rot90Fun (x : Site 2)) = (x : Site 2) from
        rot90Equiv.left_inv (x : Site 2)]; exact x.2
    · rw [mpd_rot90Inv_topSide a b c d, show rot90Inv (rot90Fun (y : Site 2)) = (y : Site 2) from
        rot90Equiv.left_inv (y : Site 2)]; exact y.2
    · exact (hxy : (openSubgraphInduce 2 (des_negConfig ω) (rect c d (-b) (-a))).Reachable _ _).map
        (mpd_inducedHomInv a b c d ω)















theorem mpd_dualCut_snd_le {p q : Site 2}
    (h : IsOpenEdge 2 (dualConfig des_cutConfig) p q) : p 1 ≤ 1 ∧ q 1 ≤ 1 := by
  obtain ⟨_hadj, hopen⟩ := h
  rw [dual_isOpen_iff_isClosed] at hopen
  have hce : (crossEdge.symm s(p, q)) = s(rot90Inv p, rot90Inv q) := by
    change (sym2Congr rot90Equiv).symm s(p, q) = s(rot90Inv p, rot90Inv q)
    rw [sym2Congr]; simp [Sym2.map_mk]
  rw [hce] at hopen
  by_contra hcon
  apply absurd hopen
  rw [des_cutConfig_open_of_not_cut]
  · simp
  · rintro ⟨c, hc⟩
    rw [Sym2.eq_iff] at hc
    rcases hc with ⟨hp, hq⟩ | ⟨hp, hq⟩
    · have hp1 : p 1 = 0 := by have := congrFun hp 0; simpa [rot90Inv] using this
      have hq1 : q 1 = 1 := by have := congrFun hq 0; simpa [rot90Inv] using this
      omega
    · have hp1 : p 1 = 1 := by have := congrFun hp 0; simpa [rot90Inv] using this
      have hq1 : q 1 = 0 := by have := congrFun hq 0; simpa [rot90Inv] using this
      omega



theorem mpd_dualCut_walk_snd_le {S : Set (Site 2)} {x y : S}
    (h : ConnectedWithin 2 (dualConfig des_cutConfig) S x y)
    (hx : (x : Site 2) 1 ≤ 1) : (y : Site 2) 1 ≤ 1 := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact hx
  | @cons a b c hab _ ih =>
    rw [openSubgraphInduce_adj, openSubgraph_adj] at hab
    exact ih (mpd_dualCut_snd_le hab).2




theorem mpd_no_dualV_box (a b h : ℤ) (hh : 2 ≤ h) :
    ¬ DualVerticalCrossing des_cutConfig a b 0 h := by
  rw [dualVerticalCrossing_iff]
  rintro ⟨x, y, hxy⟩
  have hx1 : ((⟨(x : Site 2), bottomSide_subset x.2⟩ : rect a b 0 h) : Site 2) 1 ≤ 1 := by
    change (x : Site 2) 1 ≤ 1; rw [x.2.2]; norm_num
  have hy1 := mpd_dualCut_walk_snd_le hxy hx1
  have : (y : Site 2) 1 ≤ 1 := hy1
  rw [y.2.2] at this
  omega





theorem mpd_no_H_box (w h : ℤ) (hw : 1 ≤ w) :
    ¬ HorizontalCrossing des_cutConfig 0 w 0 h := by
  rintro ⟨x, y, hxy⟩
  have hside := des_cutConfig_connectedWithin_sameSide0 hxy
  have hx0 : (x : Site 2) 0 = 0 := x.2.2
  have hy0 : (y : Site 2) 0 = w := y.2.2
  rw [hx0, hy0] at hside
  have h0 : (0 : ℤ) ≤ 0 := le_refl 0
  have : (w : ℤ) ≤ 0 := hside.mp h0
  omega











theorem mpd_matched_planarDuality_false (n : ℤ) (hn : 2 ≤ n) :
    ¬ rfr_MatchedPlanarDuality n := by
  intro h
  apply mpd_no_dualV_box 0 (n + 1) n hn
  have hmem : des_cutConfig ∈ dualVerticalCrossingEvent 0 (n + 1) 0 n := by
    apply h
    simp only [Set.mem_compl_iff, mem_horizontalCrossingEvent]
    exact mpd_no_H_box (n + 1) n (by omega)
  rwa [mem_dualVerticalCrossingEvent] at hmem









theorem mpd_corrected_box_false (n : ℤ) (hn : 1 ≤ n) :
    ¬ DualVerticalCrossing des_cutConfig (-n) 0 0 (n + 1) :=
  mpd_no_dualV_box (-n) 0 (n + 1) (by omega)













def mpd_leftReach (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) : Set (Site 2) :=
  {v | v ∈ rect 0 (n + 1) 0 n ∧ ∃ (x : Site 2) (hx : x ∈ leftSide 0 (n + 1) 0 n)
      (hv : v ∈ rect 0 (n + 1) 0 n),
      ConnectedWithin 2 ω (rect 0 (n + 1) 0 n) ⟨x, leftSide_subset hx⟩ ⟨v, hv⟩}

theorem mpd_leftReach_subset_box (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    mpd_leftReach ω n ⊆ rect 0 (n + 1) 0 n := fun _ hv => hv.1


theorem mpd_leftReach_finite (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    (mpd_leftReach ω n).Finite :=
  (rect_finite 0 (n + 1) 0 n).subset (mpd_leftReach_subset_box ω n)


theorem mpd_horizontal_iff_right_in_leftReach (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    HorizontalCrossing ω 0 (n + 1) 0 n ↔
      ∃ y : Site 2, y ∈ rightSide 0 (n + 1) 0 n ∧ y ∈ mpd_leftReach ω n := by
  constructor
  · rintro ⟨x, y, hxy⟩
    exact ⟨y, y.2, rightSide_subset y.2, x, x.2, rightSide_subset y.2, hxy⟩
  · rintro ⟨y, hyR, _hybox, x, hxL, hyb, hconn⟩
    exact ⟨⟨x, hxL⟩, ⟨y, hyR⟩, hconn⟩


theorem mpd_leftSide_subset_leftReach (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    {x : Site 2} (hx : x ∈ leftSide 0 (n + 1) 0 n) : x ∈ mpd_leftReach ω n :=
  ⟨leftSide_subset hx, x, hx, leftSide_subset hx,
    connectedWithin_refl ω (rect 0 (n + 1) 0 n) ⟨x, leftSide_subset hx⟩⟩


theorem mpd_rightSide_notin_leftReach (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hnoH : ¬ HorizontalCrossing ω 0 (n + 1) 0 n) {y : Site 2}
    (hy : y ∈ rightSide 0 (n + 1) 0 n) : y ∉ mpd_leftReach ω n := fun hyL =>
  hnoH ((mpd_horizontal_iff_right_in_leftReach ω n).mpr ⟨y, hy, hyL⟩)






theorem mpd_leftReach_separates (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hnoH : ¬ HorizontalCrossing ω 0 (n + 1) 0 n)
    {x y : Site 2} (hx : x ∈ leftSide 0 (n + 1) 0 n) (hy : y ∈ rightSide 0 (n + 1) 0 n) :
    ¬ (latticeMinusBarrier (mpd_leftReach ω n)).Reachable x y :=
  not_reachable_latticeMinusBarrier (mpd_leftReach ω n)
    (mpd_leftSide_subset_leftReach ω n hx) (mpd_rightSide_notin_leftReach ω n hnoH hy)




theorem mpd_escape_crossCount_odd (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hnoH : ¬ HorizontalCrossing ω 0 (n + 1) 0 n)
    {x y : Site 2} (hx : x ∈ leftSide 0 (n + 1) 0 n) (hy : y ∈ rightSide 0 (n + 1) 0 n)
    (w : (hypercubicLattice 2).Walk x y) :
    ¬ Even (crossCount (mpd_leftReach ω n) w) :=
  crossCount_odd_of_separated (mpd_leftReach ω n)
    (mpd_leftSide_subset_leftReach ω n hx) (mpd_rightSide_notin_leftReach ω n hnoH hy) w


theorem mpd_leftReach_extend (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {v w : Site 2}
    (hv : v ∈ mpd_leftReach ω n) (hwbox : w ∈ rect 0 (n + 1) 0 n)
    (hadj : (hypercubicLattice 2).Adj v w) (hopen : ω s(v, w) = true) :
    w ∈ mpd_leftReach ω n := by
  obtain ⟨_hvbox, x, hxL, hvbox', hconn⟩ := hv
  refine ⟨hwbox, x, hxL, hwbox, ?_⟩
  have hstep : (openSubgraphInduce 2 ω (rect 0 (n + 1) 0 n)).Adj ⟨v, hvbox'⟩ ⟨w, hwbox⟩ := by
    rw [openSubgraphInduce_adj]; exact ⟨hadj, hopen⟩
  exact hconn.trans hstep.reachable


theorem mpd_leftReach_boundary_closed (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    {p q : Site 2} (hadj : (hypercubicLattice 2).Adj p q)
    (hbd : bdEdge (mpd_leftReach ω n) s(p, q))
    (hpbox : p ∈ rect 0 (n + 1) 0 n) (hqbox : q ∈ rect 0 (n + 1) 0 n) :
    ω s(p, q) = false := by
  rw [bdEdge_mk] at hbd
  by_cases hp : p ∈ mpd_leftReach ω n
  · by_contra h
    rw [Bool.not_eq_false] at h
    exact (hbd.mp hp) (mpd_leftReach_extend ω n hp hqbox hadj h)
  · have hq : q ∈ mpd_leftReach ω n := by by_contra hqn; exact hp (hbd.mpr hqn)
    rw [Sym2.eq_swap]
    by_contra h
    rw [Bool.not_eq_false] at h
    exact hp (mpd_leftReach_extend ω n hq hpbox hadj.symm h)


theorem mpd_leftReach_barrier_dual_open (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    {p q : Site 2} (hadj : (hypercubicLattice 2).Adj p q)
    (hbd : bdEdge (mpd_leftReach ω n) s(p, q))
    (hpbox : p ∈ rect 0 (n + 1) 0 n) (hqbox : q ∈ rect 0 (n + 1) 0 n) :
    dualConfig ω (crossEdge s(p, q)) = true := by
  rw [StatMech.RSW.dualCross_open_iff_closed]
  exact mpd_leftReach_boundary_closed ω n hadj hbd hpbox hqbox



theorem mpd_edgeBoundary_nonempty (ω : ConfigSpace (Sym2 (Site 2)))
    {n : ℤ} (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 (n + 1) 0 n) :
    (edgeBoundary 2 (mpd_leftReach ω n)).Nonempty := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  have hxL : (![0, 0] : Site 2) ∈ leftSide 0 ((m : ℤ) + 1) 0 (m : ℤ) := by
    refine ⟨?_, by simp⟩
    rw [mem_rect]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact ⟨le_refl 0, by positivity, le_refl 0, by positivity⟩
  have hyR : (![(m : ℤ) + 1, 0] : Site 2) ∈ rightSide 0 ((m : ℤ) + 1) 0 (m : ℤ) := by
    refine ⟨?_, by simp⟩
    rw [mem_rect]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact ⟨by positivity, le_refl _, le_refl 0, by positivity⟩
  obtain ⟨w⟩ := jex_lattice_walk_row 0 (m + 1)
  have hw : (hypercubicLattice 2).Walk (![0, 0] : Site 2) (![((m : ℤ) + 1), 0]) := by
    have he : (![((m + 1 : ℕ) : ℤ), 0] : Site 2) = (![(m : ℤ) + 1, 0] : Site 2) := by
      funext i; fin_cases i <;> simp
    rw [he] at w; exact w
  exact edgeBoundary_nonempty_of_walk (mpd_leftReach ω (m : ℤ)) hw
    (mpd_leftSide_subset_leftReach ω (m : ℤ) hxL)
    (mpd_rightSide_notin_leftReach ω (m : ℤ) hnoH hyR)








theorem mpd_exists_dualCircuit (ω : ConfigSpace (Sym2 (Site 2)))
    {n : ℤ} (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 (n + 1) 0 n) :
    ∃ (u : Site 2) (c : (faceBoundaryGraph (mpd_leftReach ω n)).Walk u u), c.IsCycle := by
  obtain ⟨⟨a, b⟩, hab⟩ := mpd_edgeBoundary_nonempty ω hn hnoH
  exact exists_dualCircuit_of_finite_of_edgeBoundary (mpd_leftReach ω n)
    (mpd_leftReach_finite ω n) hab

















def mpd_MatchedFrameDualV (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) : Prop :=
  DualVerticalCrossing ω (-n) 0 0 (n + 1)







theorem mpd_dichotomy_of_matchedFrame (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (_hnoH : ¬ HorizontalCrossing ω 0 (n + 1) 0 n) (h : mpd_MatchedFrameDualV ω n) :
    HorizontalCrossing ω 0 (n + 1) 0 n ∨ DualVerticalCrossing ω (-n) 0 0 (n + 1) :=
  Or.inr h


theorem mpd_botCfg_dual_allOpen (e : Sym2 (Site 2)) : dualConfig bcc_botCfg e = true :=
  bcc_dualConfig_bot e



def mpd_dualBotHom (S : Set (Site 2)) :
    ((hypercubicLattice 2).induce S) →g (openSubgraphInduce 2 (dualConfig bcc_botCfg) S) where
  toFun := id
  map_rel' := by
    intro x y h
    rw [openSubgraphInduce_adj, openSubgraph_adj]
    rw [SimpleGraph.induce_adj] at h
    exact ⟨h, bcc_dualConfig_bot _⟩





theorem mpd_botCfg_dualV_col (a b c d x0 : ℤ) (hx : a ≤ x0 ∧ x0 ≤ b) (hcd : c ≤ d) :
    DualVerticalCrossing bcc_botCfg a b c d := by
  unfold DualVerticalCrossing VerticalCrossing
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ d - c)
  set R := rect a b c d with hR
  have hbmem : (![x0, c] : Site 2) ∈ bottomSide a b c d := by
    refine ⟨?_, by simp⟩; rw [mem_rect]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; exact ⟨hx.1, hx.2, by omega, hcd⟩
  have htmem : (![x0, d] : Site 2) ∈ topSide a b c d := by
    refine ⟨?_, by simp⟩; rw [mem_rect]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; exact ⟨hx.1, hx.2, hcd, le_refl _⟩
  have hupd : ∀ t : ℕ, Function.update (![x0, c] : Site 2) 1 ((![x0, c] : Site 2) 1 + (t : ℤ))
      = ![x0, c + (t : ℤ)] := by
    intro t; funext i; fin_cases i <;> simp [Function.update]
  have hseg := segment_connectedWithin (d := 2) R (1 : Fin 2) (![x0, c] : Site 2) k
    (fun t htle => by
      rw [hR, hupd t, mem_rect]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      exact ⟨hx.1, hx.2, by omega, by omega⟩)
  obtain ⟨w⟩ := hseg
  have wmap := w.map (mpd_dualBotHom R)
  refine ⟨⟨![x0, c], hbmem⟩, ⟨![x0, d], htmem⟩, ?_⟩
  change (openSubgraphInduce 2 (dualConfig bcc_botCfg) R).Reachable
    ⟨![x0, c], bottomSide_subset hbmem⟩ ⟨![x0, d], topSide_subset htmem⟩
  refine (wmap.copy ?_ ?_).reachable
  · apply Subtype.ext
    change Function.update (![x0, c] : Site 2) 1 ((![x0, c] : Site 2) 1 + (0 : ℤ)) = ![x0, c]
    funext i; fin_cases i <;> simp [Function.update]
  · apply Subtype.ext
    change Function.update (![x0, c] : Site 2) 1 ((![x0, c] : Site 2) 1 + ((k : ℕ) : ℤ)) = ![x0, d]
    have hck : (![x0, c] : Site 2) 1 + ((k : ℕ) : ℤ) = d := by simp; omega
    rw [hck]
    funext i; fin_cases i <;> simp [Function.update]




theorem mpd_botCfg_noH (n : ℤ) (hn : 0 ≤ n) :
    ¬ HorizontalCrossing bcc_botCfg 0 (n + 1) 0 n := by
  rintro ⟨x, y, hxy⟩
  have heq := bcc_connWithin_bot_eq hxy
  have hval : (x : Site 2) = (y : Site 2) := congrArg Subtype.val heq
  have hx0 : (x : Site 2) 0 = 0 := x.2.2
  have hy0 : (y : Site 2) 0 = n + 1 := y.2.2
  rw [hval, hy0] at hx0
  omega






theorem mpd_matchedFrame_nonvacuous (n : ℤ) (hn : 0 ≤ n) :
    ¬ HorizontalCrossing bcc_botCfg 0 (n + 1) 0 n ∧ mpd_MatchedFrameDualV bcc_botCfg n :=
  ⟨mpd_botCfg_noH n hn,
    mpd_botCfg_dualV_col (-n) 0 0 (n + 1) 0 ⟨by omega, le_refl 0⟩ (by omega)⟩









theorem mpd_literal_vs_honest_boxes (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    (DualVerticalCrossing ω 0 (n + 1) 0 n
        ↔ HorizontalCrossing (des_negConfig ω) 0 n (-(n + 1)) 0) ∧
      (mpd_MatchedFrameDualV ω n
        ↔ HorizontalCrossing (des_negConfig ω) 0 (n + 1) 0 n) := by
  refine ⟨mpd_dualV_iff_negH ω 0 (n + 1) 0 n, ?_⟩
  unfold mpd_MatchedFrameDualV
  have := mpd_dualV_iff_negH ω (-n) 0 0 (n + 1)
  simpa using this






theorem mpd_both_plain_targets_false (n : ℤ) (hn : 2 ≤ n) :
    ¬ HorizontalCrossing des_cutConfig 0 (n + 1) 0 n ∧
      ¬ DualVerticalCrossing des_cutConfig 0 (n + 1) 0 n ∧
      ¬ DualVerticalCrossing des_cutConfig (-n) 0 0 (n + 1) :=
  ⟨mpd_no_H_box (n + 1) n (by omega),
   mpd_no_dualV_box 0 (n + 1) n hn,
   mpd_corrected_box_false n (by omega)⟩

end Universality

end StatMech
