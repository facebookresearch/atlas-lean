/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
























































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.JordanExteriorClosure
import Code.Lattice.GaussBonnet
import Code.Lattice.CrossingParity
import Code.Lattice.WindingWitness
import Code.Walls.umffullrev
import Code.Walls.wndwinding

open Finset Set SimpleGraph
open scoped BigOperators

namespace StatMech

namespace Lattice











def wnu_Alt : List ℤ → Prop
  | [] => True
  | [a] => a = 1 ∨ a = -1
  | a :: b :: t => (a = 1 ∨ a = -1) ∧ b = -a ∧ wnu_Alt (b :: t)

@[simp] theorem wnu_Alt_nil : wnu_Alt [] := trivial

@[simp] theorem wnu_Alt_singleton (a : ℤ) : wnu_Alt [a] ↔ (a = 1 ∨ a = -1) := Iff.rfl

theorem wnu_Alt_cons_cons {a b : ℤ} {t : List ℤ} :
    wnu_Alt (a :: b :: t) ↔ (a = 1 ∨ a = -1) ∧ b = -a ∧ wnu_Alt (b :: t) := Iff.rfl


theorem wnu_Alt_tail {a : ℤ} {t : List ℤ} (h : wnu_Alt (a :: t)) : wnu_Alt t := by
  cases t with
  | nil => exact trivial
  | cons b t' => exact (wnu_Alt_cons_cons.mp h).2.2


theorem wnu_Alt_head_pm {a : ℤ} {t : List ℤ} (h : wnu_Alt (a :: t)) : a = 1 ∨ a = -1 := by
  cases t with
  | nil => exact h
  | cons b t' => exact (wnu_Alt_cons_cons.mp h).1





theorem wnu_altSum_mem : ∀ (L : List ℤ), wnu_Alt L →
    (L.sum = 0 ∨ (∃ s, (s = 1 ∨ s = -1) ∧ L.sum = s)) := by
  intro L
  induction L using List.twoStepInduction with
  | nil => intro _; left; simp
  | singleton a =>
    intro h
    right
    exact ⟨a, h, by simp⟩
  | cons_cons a b t ih _ =>
    intro h
    have hb : b = -a := (wnu_Alt_cons_cons.mp h).2.1
    have htail : wnu_Alt t := wnu_Alt_tail (wnu_Alt_tail h)
    have hsum : (a :: b :: t).sum = t.sum := by
      simp only [List.sum_cons, hb]; ring
    rcases ih htail with h0 | ⟨s, hs, hseq⟩
    · left; rw [hsum, h0]
    · right; exact ⟨s, hs, by rw [hsum, hseq]⟩



theorem wnu_altSum_abs_le_one (L : List ℤ) (h : wnu_Alt L) : |L.sum| ≤ 1 := by
  rcases wnu_altSum_mem L h with h0 | ⟨s, hs, hseq⟩
  · rw [h0]; decide
  · rw [hseq]; rcases hs with rfl | rfl <;> decide



theorem wnu_altSum_pm_one_of_ne_zero (L : List ℤ) (h : wnu_Alt L) (hne : L.sum ≠ 0) :
    L.sum = 1 ∨ L.sum = -1 := by
  rcases wnu_altSum_mem L h with h0 | ⟨s, hs, hseq⟩
  · exact absurd h0 hne
  · rw [hseq]; exact hs








theorem wnu_sum_filter_ne_zero (L : List ℤ) :
    L.sum = (L.filter (fun s => s ≠ 0)).sum := by
  classical
  induction L with
  | nil => simp
  | cons a t ih =>
    by_cases ha : a = 0
    · rw [List.filter_cons_of_neg (by simp [ha]), List.sum_cons, ha, zero_add, ih]
    · rw [List.filter_cons_of_pos (by simp [ha]), List.sum_cons, List.sum_cons, ih]





theorem wnu_signedCross_eq_filter_sum (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) :
    wnd_signedCross z w =
      ((w.darts.map (fun d => wnd_signStep z d.toProd.1 d.toProd.2)).filter
        (fun s => s ≠ 0)).sum := by
  classical
  unfold wnd_signedCross
  exact wnu_sum_filter_ne_zero _











noncomputable def wnu_signedList (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) : List ℤ :=
  (w.darts.map (fun d => wnd_signStep z d.toProd.1 d.toProd.2)).filter (fun s => s ≠ 0)


theorem wnu_signedList_sum (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) :
    (wnu_signedList z w).sum = wnd_signedCross z w :=
  (wnu_signedCross_eq_filter_sum z w).symm








def wnu_Alternates (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) : Prop :=
  wnu_Alt (wnu_signedList z w)





theorem wnu_signedCross_abs_le_one_of_alternates (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) (halt : wnu_Alternates z w) :
    |wnd_signedCross z w| ≤ 1 := by
  rw [← wnu_signedList_sum z w]
  exact wnu_altSum_abs_le_one _ halt




theorem wnu_signedCross_pm_one_of_alternates_of_ne_zero (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) (halt : wnu_Alternates z w)
    (hne : wnd_signedCross z w ≠ 0) :
    wnd_signedCross z w = 1 ∨ wnd_signedCross z w = -1 := by
  rw [← wnu_signedList_sum z w] at hne ⊢
  exact wnu_altSum_pm_one_of_ne_zero _ halt hne





theorem wnu_signedCross_pm_one_of_alternates (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) (halt : wnu_Alternates z w)
    (hodd : ¬ Even (jec_rayCount z w)) :
    wnd_signedCross z w = 1 ∨ wnd_signedCross z w = -1 :=
  wnu_signedCross_pm_one_of_alternates_of_ne_zero z w halt
    (wnd_signedCross_ne_zero_of_rayCount_odd z w hodd)















theorem wnu_signedCrossPMone_of_alternates (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (z : Site 2)
    (halt : wnu_Alternates z (olb_orbitLoop K hK a.1 a.2))
    (hodd : ¬ Even (jec_rayCount z (olb_orbitLoop K hK a.1 a.2))) :
    wnd_SignedCrossPMone K hK a z := by
  unfold wnd_SignedCrossPMone
  exact wnu_signedCross_pm_one_of_alternates z (olb_orbitLoop K hK a.1 a.2) halt hodd




theorem wnu_revCount_pm_one_of_alternates_bridge (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (z : Site 2)
    (halt : wnu_Alternates z (olb_orbitLoop K hK a.1 a.2))
    (hodd : ¬ Even (jec_rayCount z (olb_orbitLoop K hK a.1 a.2)))
    (hbridge : wnd_SignedCrossEqRevCount K hK a z) :
    revCount K a = 1 ∨ revCount K a = -1 :=
  wnd_revCount_pm_one_of_residues K hK a z hbridge
    (wnu_signedCrossPMone_of_alternates K hK a z halt hodd)





theorem wnu_eulerCharOne_of_alternates_bridge (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (z : Site 2)
    (hp : 3 ≤ dartOrbitPeriod K a)
    (halt : wnu_Alternates z (olb_orbitLoop K hK a.1 a.2))
    (hodd : ¬ Even (jec_rayCount z (olb_orbitLoop K hK a.1 a.2)))
    (hbridge : wnd_SignedCrossEqRevCount K hK a z) :
    EulerCharOne K a :=
  wnd_eulerCharOne_of_residues K hK a z hp hbridge
    (wnu_signedCrossPMone_of_alternates K hK a z halt hodd)






















theorem wnu_not_alt_oneOne : ¬ wnu_Alt [1, 1] := by
  rw [wnu_Alt_cons_cons]
  rintro ⟨_, h, _⟩
  exact absurd h (by decide)



theorem wnu_unitSquare_signedList :
    wnu_signedList (![1, 1] : Site 2) wwit_unitSquareLoop = [1] := by
  unfold wnu_signedList wwit_unitSquareLoop
  simp only [SimpleGraph.Walk.darts_append, SimpleGraph.Walk.darts_copy,
    SimpleGraph.Walk.darts_reverse, List.map_append, List.map_reverse, List.map_map]
  decide



theorem wnu_unitSquare_alternates :
    wnu_Alternates (![1, 1] : Site 2) wwit_unitSquareLoop := by
  unfold wnu_Alternates
  rw [wnu_unitSquare_signedList]
  exact Or.inl rfl




theorem wnu_unitSquare_signedCross_abs_le_one :
    |wnd_signedCross (![1, 1] : Site 2) wwit_unitSquareLoop| ≤ 1 :=
  wnu_signedCross_abs_le_one_of_alternates _ _ wnu_unitSquare_alternates



noncomputable def wnu_doubleSquare : (hypercubicLattice 2).Walk ![0, 0] ![0, 0] :=
  wwit_unitSquareLoop.append wwit_unitSquareLoop



theorem wnu_doubleSquare_signedList :
    wnu_signedList (![1, 1] : Site 2) wnu_doubleSquare = [1, 1] := by
  unfold wnu_doubleSquare wnu_signedList wwit_unitSquareLoop
  simp only [SimpleGraph.Walk.darts_append, SimpleGraph.Walk.darts_copy,
    SimpleGraph.Walk.darts_reverse, List.map_append, List.map_reverse, List.map_map]
  decide




theorem wnu_doubleSquare_not_alternates :
    ¬ wnu_Alternates (![1, 1] : Site 2) wnu_doubleSquare := by
  unfold wnu_Alternates
  rw [wnu_doubleSquare_signedList]
  exact wnu_not_alt_oneOne




theorem wnu_doubleSquare_signedCross_two :
    wnd_signedCross (![1, 1] : Site 2) wnu_doubleSquare = 2 := by
  unfold wnu_doubleSquare
  rw [wnd_signedCross_append, wnd_unitSquareLoop_signedCross]; norm_num


theorem wnu_doubleSquare_not_pm_one :
    ¬ (wnd_signedCross (![1, 1] : Site 2) wnu_doubleSquare = 1 ∨
       wnd_signedCross (![1, 1] : Site 2) wnu_doubleSquare = -1) := by
  rw [wnu_doubleSquare_signedCross_two]; decide





noncomputable def wnu_LtrominoLoop : (hypercubicLattice 2).Walk ![0, 0] ![0, 0] :=
  let a : (hypercubicLattice 2).Walk ![0, 0] ![2, 0] :=
    (jec_hsegRight 0 0 2).copy rfl (by ext i; fin_cases i <;> simp)
  let b : (hypercubicLattice 2).Walk ![2, 0] ![2, 1] :=
    (jec_vsegUp 2 0 1).copy rfl (by ext i; fin_cases i <;> simp)
  let c : (hypercubicLattice 2).Walk ![2, 1] ![1, 1] :=
    ((jec_hsegRight 1 1 1).copy rfl (by ext i; fin_cases i <;> simp)).reverse
  let d : (hypercubicLattice 2).Walk ![1, 1] ![1, 2] :=
    (jec_vsegUp 1 1 1).copy rfl (by ext i; fin_cases i <;> simp)
  let e : (hypercubicLattice 2).Walk ![1, 2] ![0, 2] :=
    ((jec_hsegRight 2 0 1).copy rfl (by ext i; fin_cases i <;> simp)).reverse
  let f : (hypercubicLattice 2).Walk ![0, 2] ![0, 0] :=
    ((jec_vsegUp 0 0 2).copy rfl (by ext i; fin_cases i <;> simp)).reverse
  a.append (b.append (c.append (d.append (e.append f))))





theorem wnu_Ltromino_signedList :
    wnu_signedList (![1, 1] : Site 2) wnu_LtrominoLoop = [-1] := by
  unfold wnu_signedList wnu_LtrominoLoop
  simp only [SimpleGraph.Walk.darts_append, SimpleGraph.Walk.darts_copy,
    SimpleGraph.Walk.darts_reverse, List.map_append, List.map_reverse, List.map_map]
  decide



theorem wnu_Ltromino_alternates :
    wnu_Alternates (![1, 1] : Site 2) wnu_LtrominoLoop := by
  unfold wnu_Alternates
  rw [wnu_Ltromino_signedList]
  exact Or.inr rfl



theorem wnu_Ltromino_signedCross_abs_le_one :
    |wnd_signedCross (![1, 1] : Site 2) wnu_LtrominoLoop| ≤ 1 :=
  wnu_signedCross_abs_le_one_of_alternates _ _ wnu_Ltromino_alternates


















































end Lattice

end StatMech
