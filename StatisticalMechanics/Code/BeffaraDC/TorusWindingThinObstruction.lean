/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

















import Code.BeffaraDC.LongRectangleTorusCover

open SimpleGraph Set

namespace StatMech.BeffaraDC

open StatMech.Lattice
open StatMech.RSW.Box

local instance windingThinCounterexample_periodFact :
    Fact (2 < bdcLongRectanglePeriod 2 1) := by
  constructor
  norm_num [bdcLongRectanglePeriod]

local instance windingThinCounterexample_eightFact : Fact (2 < (8 : ℕ)) :=
  ⟨by norm_num⟩





noncomputable def windingThinCounterexampleConfig : TorusAmbientConfig 8 :=
  fun e =>
    match (torusEdgeCodeEquiv 8).symm e with
    | ((x, y), TorusEdgeOrientation.horizontal) => decide (y = 0 ∨ x = y)
    | ((x, y), TorusEdgeOrientation.vertical) => decide (x = y + 1)

@[simp] theorem windingThinCounterexampleConfig_horizontal (x y : ZMod 8) :
    windingThinCounterexampleConfig (torusHorizontalEdge 8 x y) =
      decide (y = 0 ∨ x = y) := by
  have hcode : (torusEdgeCodeEquiv 8).symm
      (torusHorizontalEdge 8 x y) =
        ((x, y), TorusEdgeOrientation.horizontal) := by
    apply (torusEdgeCodeEquiv 8).injective
    simp [torusEdgeCodeEquiv_apply, torusEdgeOfCode]
  rw [windingThinCounterexampleConfig, hcode]

@[simp] theorem windingThinCounterexampleConfig_vertical (x y : ZMod 8) :
    windingThinCounterexampleConfig (torusVerticalEdge 8 x y) =
      decide (x = y + 1) := by
  have hcode : (torusEdgeCodeEquiv 8).symm
      (torusVerticalEdge 8 x y) =
        ((x, y), TorusEdgeOrientation.vertical) := by
    apply (torusEdgeCodeEquiv 8).injective
    simp [torusEdgeCodeEquiv_apply, torusEdgeOfCode]
  rw [windingThinCounterexampleConfig, hcode]


theorem windingThinCounterexample_diagHorizontal (t : ℤ) :
    IsOpenEdge 2 (torusPlanarPullback 8 windingThinCounterexampleConfig)
      ![t, t] ![t + 1, t] := by
  refine ⟨sw_adj_horizSucc t t, ?_⟩
  rw [torusPlanarPullback_horizontal,
    windingThinCounterexampleConfig_horizontal]
  simp


theorem windingThinCounterexample_diagVertical (t : ℤ) :
    IsOpenEdge 2 (torusPlanarPullback 8 windingThinCounterexampleConfig)
      ![t + 1, t] ![t + 1, t + 1] := by
  refine ⟨sw_adj_vertSucc (t + 1) t, ?_⟩
  rw [torusPlanarPullback_vertical,
    windingThinCounterexampleConfig_vertical]
  simp



theorem windingThinCounterexample_rowEight (t : ℤ) :
    IsOpenEdge 2 (torusPlanarPullback 8 windingThinCounterexampleConfig)
      ![t, 8] ![t + 1, 8] := by
  refine ⟨sw_adj_horizSucc 8 t, ?_⟩
  rw [torusPlanarPullback_horizontal,
    windingThinCounterexampleConfig_horizontal]
  rw [decide_eq_true_eq]
  left
  decide



theorem windingThinCounterexample_winds :
    bdcTorusVerticalWinding 8 windingThinCounterexampleConfig := by
  let omega := torusPlanarPullback 8 windingThinCounterexampleConfig
  have hd0 : Connected 2 omega ![0, 0] ![1, 1] :=
    (windingThinCounterexample_diagHorizontal 0).connected.trans
      (windingThinCounterexample_diagVertical 0).connected
  have hd1 : Connected 2 omega ![1, 1] ![2, 2] :=
    (windingThinCounterexample_diagHorizontal 1).connected.trans
      (windingThinCounterexample_diagVertical 1).connected
  have hd2 : Connected 2 omega ![2, 2] ![3, 3] :=
    (windingThinCounterexample_diagHorizontal 2).connected.trans
      (windingThinCounterexample_diagVertical 2).connected
  have hd3 : Connected 2 omega ![3, 3] ![4, 4] :=
    (windingThinCounterexample_diagHorizontal 3).connected.trans
      (windingThinCounterexample_diagVertical 3).connected
  have hd4 : Connected 2 omega ![4, 4] ![5, 5] :=
    (windingThinCounterexample_diagHorizontal 4).connected.trans
      (windingThinCounterexample_diagVertical 4).connected
  have hd5 : Connected 2 omega ![5, 5] ![6, 6] :=
    (windingThinCounterexample_diagHorizontal 5).connected.trans
      (windingThinCounterexample_diagVertical 5).connected
  have hd6 : Connected 2 omega ![6, 6] ![7, 7] :=
    (windingThinCounterexample_diagHorizontal 6).connected.trans
      (windingThinCounterexample_diagVertical 6).connected
  have hd7 : Connected 2 omega ![7, 7] ![8, 8] :=
    (windingThinCounterexample_diagHorizontal 7).connected.trans
      (windingThinCounterexample_diagVertical 7).connected
  have hr : Connected 2 omega ![0, 8] ![8, 8] :=
    (windingThinCounterexample_rowEight 0).connected |>.trans
    ((windingThinCounterexample_rowEight 1).connected |>.trans
    ((windingThinCounterexample_rowEight 2).connected |>.trans
    ((windingThinCounterexample_rowEight 3).connected |>.trans
    ((windingThinCounterexample_rowEight 4).connected |>.trans
    ((windingThinCounterexample_rowEight 5).connected |>.trans
    ((windingThinCounterexample_rowEight 6).connected |>.trans
      (windingThinCounterexample_rowEight 7).connected))))))
  refine ⟨![0, 0], ?_⟩
  have hconn := hd0.trans (hd1.trans (hd2.trans (hd3.trans
    (hd4.trans (hd5.trans (hd6.trans hd7))))))
  convert hconn.trans hr.symm using 1
  ext i
  fin_cases i <;> norm_num




theorem windingThinCounterexample_vertical_iff (x y : ℤ) :
    torusPlanarPullback 8 windingThinCounterexampleConfig
        s(![x, y], ![x, y + 1]) = true ↔
      (x : ZMod 8) = (y : ZMod 8) + 1 := by
  rw [torusPlanarPullback_vertical,
    windingThinCounterexampleConfig_vertical, decide_eq_true_eq]



theorem windingThinCounterexample_cut_step
    {a c h : ℤ} {p q : Site 2}
    (hp : p ∈ rect a (a + 2) c (c + 4))
    (hq : q ∈ rect a (a + 2) c (c + 4))
    (hadj : (hypercubicLattice 2).Adj p q)
    (hopen : torusPlanarPullback 8 windingThinCounterexampleConfig s(p, q) = true)
    (hple : p 1 ≤ h)
    (hmiss : ∀ x : ℤ, a ≤ x → x ≤ a + 2 →
      (x : ZMod 8) ≠ (h : ZMod 8) + 1) :
    q 1 ≤ h := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
  rw [mem_rect] at hp hq
  by_contra hqle
  push Not at hqle
  have hp1 : p 1 = h := by omega
  have hq1 : q 1 = h + 1 := by omega
  have hpq0 : p 0 = q 0 := by omega
  have hpe : p = ![p 0, h] := by
    funext i
    fin_cases i <;> simp [hp1]
  have hqe : q = ![p 0, h + 1] := by
    funext i
    fin_cases i <;> simp [hpq0.symm, hq1]
  have hrung : (p 0 : ZMod 8) = (h : ZMod 8) + 1 := by
    apply (windingThinCounterexample_vertical_iff (p 0) h).mp
    rw [hpe, hqe] at hopen
    simpa using hopen
  exact (hmiss (p 0) hp.1 hp.2.1) hrung


theorem windingThinCounterexample_cut_walk
    {a c h : ℤ}
    (hmiss : ∀ x : ℤ, a ≤ x → x ≤ a + 2 →
      (x : ZMod 8) ≠ (h : ZMod 8) + 1)
    {p q : (rect a (a + 2) c (c + 4) : Set (Site 2))}
    (w : (openSubgraphInduce 2
      (torusPlanarPullback 8 windingThinCounterexampleConfig)
      (rect a (a + 2) c (c + 4))).Walk p q)
    (hp : (p : Site 2) 1 ≤ h) :
    (q : Site 2) 1 ≤ h := by
  induction w with
  | nil => exact hp
  | @cons u v z huv _ ih =>
      rw [openSubgraphInduce_adj, openSubgraph_adj] at huv
      exact ih (windingThinCounterexample_cut_step u.2 v.2 huv.1 huv.2 hp hmiss)


theorem windingThinCounterexample_no_vertical_of_missing
    {a c h : ℤ} (hch : c ≤ h) (hhc : h < c + 4)
    (hmiss : ∀ x : ℤ, a ≤ x → x ≤ a + 2 →
      (x : ZMod 8) ≠ (h : ZMod 8) + 1) :
    ¬ VerticalCrossing
      (torusPlanarPullback 8 windingThinCounterexampleConfig)
      a (a + 2) c (c + 4) := by
  rintro ⟨p, q, hpq⟩
  have hp1 : (p : Site 2) 1 = c := p.2.2
  have hq1 : (q : Site 2) 1 = c + 4 := q.2.2
  have hbound := windingThinCounterexample_cut_walk hmiss hpq.some
    (by rw [hp1]; exact hch)
  rw [hq1] at hbound
  omega





theorem windingThinCounterexample_exists_missing
    (a c : ℤ) (ha0 : 0 ≤ a) (ha7 : a ≤ 7) (hc : c = 0 ∨ c = 4) :
    ∃ h : ℤ, c ≤ h ∧ h < c + 4 ∧
      ∀ x : ℤ, a ≤ x → x ≤ a + 2 →
        (x : ZMod 8) ≠ (h : ZMod 8) + 1 := by
  rcases hc with rfl | rfl
  · interval_cases a
    · refine ⟨2, by norm_num, by norm_num, ?_⟩
      intro x hx0 hx2; interval_cases x <;> decide
    · refine ⟨3, by norm_num, by norm_num, ?_⟩
      intro x hx0 hx2; interval_cases x <;> decide
    · refine ⟨0, by norm_num, by norm_num, ?_⟩
      intro x hx0 hx2; interval_cases x <;> decide
    · refine ⟨0, by norm_num, by norm_num, ?_⟩
      intro x hx0 hx2; interval_cases x <;> decide
    · refine ⟨0, by norm_num, by norm_num, ?_⟩
      intro x hx0 hx2; interval_cases x <;> decide
    · refine ⟨0, by norm_num, by norm_num, ?_⟩
      intro x hx0 hx2; interval_cases x <;> decide
    · refine ⟨0, by norm_num, by norm_num, ?_⟩
      intro x hx0 hx2; interval_cases x <;> decide
    · refine ⟨1, by norm_num, by norm_num, ?_⟩
      intro x hx0 hx2; interval_cases x <;> decide
  · interval_cases a
    · refine ⟨4, by norm_num, by norm_num, ?_⟩
      intro x hx0 hx2; interval_cases x <;> decide
    · refine ⟨4, by norm_num, by norm_num, ?_⟩
      intro x hx0 hx2; interval_cases x <;> decide
    · refine ⟨4, by norm_num, by norm_num, ?_⟩
      intro x hx0 hx2; interval_cases x <;> decide
    · refine ⟨5, by norm_num, by norm_num, ?_⟩
      intro x hx0 hx2; interval_cases x <;> decide
    · refine ⟨6, by norm_num, by norm_num, ?_⟩
      intro x hx0 hx2; interval_cases x <;> decide
    · refine ⟨7, by norm_num, by norm_num, ?_⟩
      intro x hx0 hx2; interval_cases x <;> decide
    · refine ⟨4, by norm_num, by norm_num, ?_⟩
      intro x hx0 hx2; interval_cases x <;> decide
    · refine ⟨4, by norm_num, by norm_num, ?_⟩
      intro x hx0 hx2; interval_cases x <;> decide



theorem windingThinCounterexample_not_thin :
    ¬ bdcTorusThinCrossing 8 2 1 windingThinCounterexampleConfig := by
  rintro ⟨k, hk⟩
  let a : ℤ := bdcLongRectangleXOffset 1 k
  let c : ℤ := bdcLongRectangleYOffset 1 k
  have ha0 : 0 ≤ a := by positivity
  have ha7 : a ≤ 7 := by
    simp [a, bdcLongRectangleXOffset]
    omega
  have hc : c = 0 ∨ c = 4 := by
    simp [c, bdcLongRectangleYOffset]
    omega
  obtain ⟨h, hch, hhc, hmiss⟩ :=
    windingThinCounterexample_exists_missing a c ha0 ha7 hc
  apply windingThinCounterexample_no_vertical_of_missing hch hhc hmiss
  simpa [a, c] using hk



theorem windingThinCounterexample_winding_not_thin :
    bdcTorusVerticalWinding 8 windingThinCounterexampleConfig ∧
      ¬ bdcTorusThinCrossing 8 2 1 windingThinCounterexampleConfig :=
  ⟨windingThinCounterexample_winds, windingThinCounterexample_not_thin⟩



theorem not_bdcTorusVerticalWindingThinCover_two_one :
    ¬ BdcTorusVerticalWindingThinCover 2 1 := by
  intro h
  exact windingThinCounterexample_not_thin
    (h.toThin windingThinCounterexampleConfig windingThinCounterexample_winds)

end StatMech.BeffaraDC
