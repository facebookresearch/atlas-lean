/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





















































































































import Mathlib
import Code.Universality.HexStripWindingClose
import Code.Universality.HexInfraDisplacement
import Code.Universality.HexFiniteStripEnum

namespace StatMech.Universality

open HexWalk List Complex
open scoped BigOperators Real










theorem hexJordan_runningHead_eq_headAccum_take (h0 : ℤ) (ts : List ℤ) (k : ℕ) :
    hexStripWinding_runningHead h0 ts k = hexInfra_headAccum h0 (ts.take k) := by
  rw [hexInfra_headAccum_eq_add_sum]; rfl



theorem hexJordan_midsAux_getElem?_eq (m : ℂ) (h : ℤ) (ts : List ℤ) (k : ℕ) (hk : k ≤ ts.length) :
    (midsAux m h ts)[k]? = some (hexInfra_midAccum m h (ts.take k)) := by
  induction ts generalizing m h k with
  | nil =>
    simp only [List.length_nil, Nat.le_zero] at hk
    subst hk
    simp [midsAux]
  | cons t ts ih =>
    cases k with
    | zero => simp [midsAux]
    | succ n =>
      simp only [List.length_cons] at hk
      rw [midsAux_cons, List.getElem?_cons_succ, List.take_succ_cons, hexInfra_midAccum_cons]
      exact ih _ _ n (by omega)





theorem hexJordan_verticesAux_getElem?_eq (m : ℂ) (h : ℤ) (ts : List ℤ) (k : ℕ)
    (hk : k ≤ ts.length) :
    (verticesAux m h ts)[k]?
      = some (hexInfra_midAccum m h (ts.take k)
          + halfStep (hexInfra_headAccum h (ts.take k))) := by
  induction ts generalizing m h k with
  | nil =>
    simp only [List.length_nil, Nat.le_zero] at hk
    subst hk
    simp [verticesAux]
  | cons t ts ih =>
    cases k with
    | zero => simp [verticesAux]
    | succ n =>
      simp only [List.length_cons] at hk
      rw [verticesAux_cons, List.getElem?_cons_succ, List.take_succ_cons,
        hexInfra_midAccum_cons, hexInfra_headAccum_cons]
      exact ih _ _ n (by omega)



noncomputable def hexJordan_vertexPos (a : ℂ) (h0 : ℤ) (ts : List ℤ) (k : ℕ) : ℂ :=
  hexInfra_midAccum a h0 (ts.take k) + halfStep (hexInfra_headAccum h0 (ts.take k))





theorem hexJordan_vertexPos_ne_of_saw (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hsaw : (ofTurns a h0 ts).IsSAW) (i j : ℕ) (hi : i ≤ ts.length) (hj : j ≤ ts.length)
    (hne : i ≠ j) :
    hexJordan_vertexPos a h0 ts i ≠ hexJordan_vertexPos a h0 ts j := by
  intro heq
  unfold HexWalk.IsSAW HexWalk.vertices at hsaw
  simp only [ofTurns] at hsaw
  have hilen : i < (verticesAux a h0 ts).length := by rw [length_verticesAux]; omega
  have hjlen : j < (verticesAux a h0 ts).length := by rw [length_verticesAux]; omega
  have hvi := hexJordan_verticesAux_getElem?_eq a h0 ts i hi
  have hvj := hexJordan_verticesAux_getElem?_eq a h0 ts j hj
  have he2 : (verticesAux a h0 ts)[i]? = (verticesAux a h0 ts)[j]? := by
    rw [hvi, hvj]; unfold hexJordan_vertexPos at heq; rw [heq]
  rw [List.getElem?_eq_getElem hilen, List.getElem?_eq_getElem hjlen, Option.some.injEq] at he2
  exact hne ((List.getElem_inj hsaw).mp he2)











theorem hexJordan_sum_hexUnit_six (h : ℤ) :
    hexUnit h + hexUnit (h + 1) + hexUnit (h + 2)
      + hexUnit (h + 3) + hexUnit (h + 4) + hexUnit (h + 5) = 0 := by
  have h3 : hexUnit (h + 3) = - hexUnit h := hexUnit_add_three h
  have h4 : hexUnit (h + 4) = - hexUnit (h + 1) := by
    rw [show (h + 4 : ℤ) = (h + 1) + 3 from by ring, hexUnit_add_three]
  have h5 : hexUnit (h + 5) = - hexUnit (h + 2) := by
    rw [show (h + 5 : ℤ) = (h + 2) + 3 from by ring, hexUnit_add_three]
  rw [h3, h4, h5]; ring





theorem hexJordan_midAccum_six_left (a : ℂ) (h0 : ℤ) :
    hexInfra_midAccum a h0 [(1 : ℤ), 1, 1, 1, 1, 1] = a := by
  simp only [hexInfra_midAccum_cons, hexInfra_midAccum_nil]
  unfold HexWalk.halfStep
  have R : ∀ h : ℤ, hexUnit (h + 3) = - hexUnit h := hexUnit_add_three
  have a3 : hexUnit (h0 + 1 + 1 + 1) = - hexUnit h0 := by
    rw [show (h0 + 1 + 1 + 1 : ℤ) = h0 + 3 from by ring, R]
  have a4 : hexUnit (h0 + 1 + 1 + 1 + 1) = - hexUnit (h0 + 1) := by
    rw [show (h0 + 1 + 1 + 1 + 1 : ℤ) = (h0 + 1) + 3 from by ring, R]
  have a5 : hexUnit (h0 + 1 + 1 + 1 + 1 + 1) = - hexUnit (h0 + 1 + 1) := by
    rw [show (h0 + 1 + 1 + 1 + 1 + 1 : ℤ) = (h0 + 1 + 1) + 3 from by ring, R]
  have a6 : hexUnit (h0 + 1 + 1 + 1 + 1 + 1 + 1) = hexUnit h0 := by
    rw [show (h0 + 1 + 1 + 1 + 1 + 1 + 1 : ℤ) = h0 + 6 from by ring, hexUnit_add_six]
  rw [a3, a4, a5, a6]; ring



theorem hexJordan_midAccum_six_right (a : ℂ) (h0 : ℤ) :
    hexInfra_midAccum a h0 [(-1 : ℤ), -1, -1, -1, -1, -1] = a := by
  simp only [hexInfra_midAccum_cons, hexInfra_midAccum_nil]
  unfold HexWalk.halfStep
  have Rm : ∀ h : ℤ, hexUnit (h - 3) = - hexUnit h := by
    intro h
    have := hexUnit_add_three (h - 3)
    rw [show (h - 3 + 3 : ℤ) = h from by ring] at this
    linear_combination this
  have a3 : hexUnit (h0 + -1 + -1 + -1) = - hexUnit h0 := by
    rw [show (h0 + -1 + -1 + -1 : ℤ) = h0 - 3 from by ring, Rm]
  have a4 : hexUnit (h0 + -1 + -1 + -1 + -1) = - hexUnit (h0 + -1) := by
    rw [show (h0 + -1 + -1 + -1 + -1 : ℤ) = (h0 + -1) - 3 from by ring, Rm]
  have a5 : hexUnit (h0 + -1 + -1 + -1 + -1 + -1) = - hexUnit (h0 + -1 + -1) := by
    rw [show (h0 + -1 + -1 + -1 + -1 + -1 : ℤ) = (h0 + -1 + -1) - 3 from by ring, Rm]
  have a6 : hexUnit (h0 + -1 + -1 + -1 + -1 + -1 + -1) = hexUnit h0 := by
    rw [show (h0 + -1 + -1 + -1 + -1 + -1 + -1 : ℤ) = h0 - 6 from by ring,
      show (h0 - 6 : ℤ) = (h0 - 3) - 3 from by ring, Rm, Rm]; ring
  rw [a3, a4, a5, a6]; ring










theorem hexJordan_headAccum_append (h : ℤ) (s t : List ℤ) :
    hexInfra_headAccum h (s ++ t) = hexInfra_headAccum (hexInfra_headAccum h s) t := by
  induction s generalizing h with
  | nil => simp
  | cons x s ih => simp only [List.cons_append, hexInfra_headAccum_cons, ih]



theorem hexJordan_midAccum_append (m : ℂ) (h : ℤ) (s t : List ℤ) :
    hexInfra_midAccum m h (s ++ t)
      = hexInfra_midAccum (hexInfra_midAccum m h s) (hexInfra_headAccum h s) t := by
  induction s generalizing m h with
  | nil => simp
  | cons x s ih =>
    simp only [List.cons_append, hexInfra_midAccum_cons, hexInfra_headAccum_cons, ih]





















theorem hexJordan_no_revolution_pair (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hsaw : (ofTurns a h0 ts).IsSAW)
    (hclose : ∀ i j, i ≤ ts.length → j ≤ ts.length →
      hexStripWinding_runningHead h0 ts j = hexStripWinding_runningHead h0 ts i + 6 →
      hexJordan_vertexPos a h0 ts i = hexJordan_vertexPos a h0 ts j) :
    ∀ i j, i ≤ ts.length → j ≤ ts.length →
      hexStripWinding_runningHead h0 ts j ≠ hexStripWinding_runningHead h0 ts i + 6 := by
  intro i j hi hj heq
  have hposeq := hclose i j hi hj heq
  have hne : i ≠ j := by rintro rfl; omega
  exact hexJordan_vertexPos_ne_of_saw a h0 ts hsaw i j hi hj hne hposeq







theorem hexJordan_span_lt_six (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hlegal : (ofTurns a h0 ts).IsLegalSAW)
    (hno6 : ∀ i j, i ≤ ts.length → j ≤ ts.length →
      hexStripWinding_runningHead h0 ts j ≠ hexStripWinding_runningHead h0 ts i + 6) :
    ∀ i j, i ≤ ts.length → j ≤ ts.length →
      |hexStripWinding_runningHead h0 ts i - hexStripWinding_runningHead h0 ts j| < 6 := by
  have keyUp : ∀ i j, i ≤ j → j ≤ ts.length →
      hexStripWinding_runningHead h0 ts j - hexStripWinding_runningHead h0 ts i < 6 := by
    intro i j hij hj
    by_contra hge
    rw [not_lt] at hge
    set f := fun n => hexStripWinding_runningHead h0 ts n with hf
    have hle : f i ≤ f j := by simp only [hf]; omega
    have hm1 : min (f i) (f j) ≤ f i + 6 := by rw [min_eq_left hle]; simp only [hf]; omega
    have hm2 : f i + 6 ≤ max (f i) (f j) := by rw [max_eq_right hle]; simp only [hf]; omega
    obtain ⟨c, hci, hcj, hcm⟩ := hexUmlauf_runningHead_IVT a h0 ts hlegal i j hij hj
      (hexStripWinding_runningHead h0 ts i + 6) hm1 hm2
    exact hno6 i c (by omega) (by omega) hcm
  have keyDown : ∀ i j, i ≤ j → j ≤ ts.length →
      hexStripWinding_runningHead h0 ts i - hexStripWinding_runningHead h0 ts j < 6 := by
    intro i j hij hj
    by_contra hge
    rw [not_lt] at hge
    set f := fun n => hexStripWinding_runningHead h0 ts n with hf
    have hle : f j ≤ f i := by simp only [hf]; omega
    have hm1 : min (f i) (f j) ≤ f j + 6 := by rw [min_eq_right hle]; simp only [hf]; omega
    have hm2 : f j + 6 ≤ max (f i) (f j) := by rw [max_eq_left hle]; simp only [hf]; omega
    obtain ⟨c, hci, hcj, hcm⟩ := hexUmlauf_runningHead_IVT a h0 ts hlegal i j hij hj
      (hexStripWinding_runningHead h0 ts j + 6) hm1 hm2
    exact hno6 j c hj (by omega) hcm
  intro i j hi hj
  rw [abs_lt]
  rcases le_total i j with h | h
  · exact ⟨by have := keyUp i j h hj; omega, by have := keyDown i j h hj; omega⟩
  · exact ⟨by have := keyDown j i h hi; omega, by have := keyUp j i h hi; omega⟩






theorem hexJordan_window_of_span_attained (h0 w : ℤ) (ts : List ℤ)
    (hspan : ∀ i j, i ≤ ts.length → j ≤ ts.length →
      |hexStripWinding_runningHead h0 ts i - hexStripWinding_runningHead h0 ts j| < 6)
    (p : ℕ) (hp : p ≤ ts.length) (hpw : hexStripWinding_runningHead h0 ts p = w)
    (hfloor : ∀ k, k ≤ ts.length → w ≤ hexStripWinding_runningHead h0 ts k) :
    (∀ k, k ≤ ts.length → w ≤ hexStripWinding_runningHead h0 ts k)
      ∧ (∀ k, k ≤ ts.length → hexStripWinding_runningHead h0 ts k ≠ w + 6) := by
  refine ⟨hfloor, ?_⟩
  intro k hk heq
  have hsp := hspan p k hp hk
  rw [hpw, heq, abs_lt] at hsp
  omega


























structure HexStripSimplyConnected (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ) where
  
  H : ℤ
  
  w : ℤ
  
  hHL : w ≤ H
  
  hHU : H < w + 6
  
  hh0L : w ≤ h0
  
  hh0U : h0 < w + 6
  

  wall : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z →
      ∀ k, k ≤ ts.length → w ≤ hexStripWinding_runningHead h0 ts k
  

  attainsWall : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z →
      ∃ p, p ≤ ts.length ∧ hexStripWinding_runningHead h0 ts p = w
  


  noFullSweep : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z →
      ∀ i j, i ≤ ts.length → j ≤ ts.length →
        hexStripWinding_runningHead h0 ts j = hexStripWinding_runningHead h0 ts i + 6 →
        hexJordan_vertexPos a h0 ts i = hexJordan_vertexPos a h0 ts j

namespace HexStripSimplyConnected

variable {inRegion : ℂ → Prop} {a : ℂ} {h0 : ℤ} {z : ℂ}
  (B : HexStripSimplyConnected inRegion a h0 z)



theorem wallField (ts : List ℤ)
    (hadm : (HexWalk.ofTurns a h0 ts).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z)
    (k : ℕ) (hk : k ≤ ts.length) :
    B.w ≤ hexStripWinding_runningHead h0 ts k :=
  B.wall ts hadm k hk






theorem noFullTurnField (ts : List ℤ)
    (hadm : (HexWalk.ofTurns a h0 ts).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z)
    (k : ℕ) (hk : k ≤ ts.length) :
    hexStripWinding_runningHead h0 ts k ≠ B.w + 6 := by
  have hsaw : (HexWalk.ofTurns a h0 ts).IsSAW := hadm.1.2
  have hno6 := hexJordan_no_revolution_pair a h0 ts hsaw (B.noFullSweep ts hadm)
  have hspan := hexJordan_span_lt_six a h0 ts hadm.1 hno6
  obtain ⟨p, hp, hpw⟩ := B.attainsWall ts hadm
  exact (hexJordan_window_of_span_attained h0 B.w ts hspan p hp hpw
    (fun k hk => B.wall ts hadm k hk)).2 k hk

include B in



theorem spanField (ts : List ℤ)
    (hadm : (HexWalk.ofTurns a h0 ts).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z)
    (i j : ℕ) (hi : i ≤ ts.length) (hj : j ≤ ts.length) :
    |hexStripWinding_runningHead h0 ts i - hexStripWinding_runningHead h0 ts j| < 6 := by
  have hno6 := hexJordan_no_revolution_pair a h0 ts hadm.1.2 (B.noFullSweep ts hadm)
  exact hexJordan_span_lt_six a h0 ts hadm.1 hno6 i j hi hj

end HexStripSimplyConnected






def hexJordan_toStripBand (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (B : HexStripSimplyConnected inRegion a h0 z) :
    HexStripBand inRegion a h0 z where
  H := B.H
  w := B.w
  hHL := B.hHL
  hHU := B.hHU
  hh0L := B.hh0L
  hh0U := B.hh0U
  wall := fun ts hadm k hk => B.wallField ts hadm k hk
  noFullTurn := fun ts hadm k hk => B.noFullTurnField ts hadm k hk

@[simp] theorem hexJordan_toStripBand_H (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (B : HexStripSimplyConnected inRegion a h0 z) :
    (hexJordan_toStripBand inRegion a h0 z B).H = B.H := rfl

@[simp] theorem hexJordan_toStripBand_w (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (B : HexStripSimplyConnected inRegion a h0 z) :
    (hexJordan_toStripBand inRegion a h0 z B).w = B.w := rfl












def hexJordan_stripWinding (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (B : HexStripSimplyConnected inRegion a h0 z) :
    HexStripWinding inRegion a h0 z :=
  hexUmlauf_stripWinding_of_band inRegion a h0 z (hexJordan_toStripBand inRegion a h0 z B)

@[simp] theorem hexJordan_stripWinding_H (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (B : HexStripSimplyConnected inRegion a h0 z) :
    (hexJordan_stripWinding inRegion a h0 z B).H = B.H := rfl





theorem hexJordan_bound (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (B : HexStripSimplyConnected inRegion a h0 z) (ts : List ℤ)
    (hadm : (HexWalk.ofTurns a h0 ts).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z) :
    |hexInfra_headAccum h0 ts - B.H| < 6 :=
  (hexJordan_stripWinding inRegion a h0 z B).bound ts hadm







def hexJordan_toWindingBound (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (B : HexStripSimplyConnected inRegion a h0 z)
    (hsideExit : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW
        ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z →
        hexInfra_midAccum a h0 ts + HexWalk.halfStep (hexInfra_headAccum h0 ts)
          = z + HexWalk.halfStep B.H) :
    HexWindingBound inRegion a h0 z :=
  hexStripWinding_toWindingBound inRegion a h0 z (hexJordan_stripWinding inRegion a h0 z B)
    hsideExit













theorem hexJordan_six_left_not_saw (a : ℂ) (h0 : ℤ) (s r : List ℤ)
    (hsaw : (ofTurns a h0 (s ++ ([(1 : ℤ), 1, 1, 1, 1, 1] ++ r))).IsSAW) : False := by
  set ts := s ++ ([(1 : ℤ), 1, 1, 1, 1, 1] ++ r) with hts
  have hk1 : ts.take s.length = s := by rw [hts, List.take_append]; simp
  have hk2 : ts.take (s.length + 6) = s ++ [(1 : ℤ), 1, 1, 1, 1, 1] := by
    rw [hts, List.take_append]; simp
  have hpos : hexJordan_vertexPos a h0 ts s.length
      = hexJordan_vertexPos a h0 ts (s.length + 6) := by
    unfold hexJordan_vertexPos
    rw [hk1, hk2, hexJordan_midAccum_append, hexJordan_headAccum_append,
      hexJordan_midAccum_six_left]
    have hh : hexInfra_headAccum (hexInfra_headAccum h0 s) [(1 : ℤ), 1, 1, 1, 1, 1]
        = hexInfra_headAccum h0 s + 6 := by
      simp only [hexInfra_headAccum_cons, hexInfra_headAccum_nil]; ring
    rw [hh, hexStrip_halfStep_add6]
  have hlen : s.length + 6 ≤ ts.length := by
    rw [hts]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
  exact hexJordan_vertexPos_ne_of_saw a h0 ts hsaw s.length (s.length + 6) (by omega) hlen
    (by omega) hpos





theorem hexJordan_six_right_not_saw (a : ℂ) (h0 : ℤ) (s r : List ℤ)
    (hsaw : (ofTurns a h0 (s ++ ([(-1 : ℤ), -1, -1, -1, -1, -1] ++ r))).IsSAW) : False := by
  set ts := s ++ ([(-1 : ℤ), -1, -1, -1, -1, -1] ++ r) with hts
  have hk1 : ts.take s.length = s := by rw [hts, List.take_append]; simp
  have hk2 : ts.take (s.length + 6) = s ++ [(-1 : ℤ), -1, -1, -1, -1, -1] := by
    rw [hts, List.take_append]; simp
  have hpos : hexJordan_vertexPos a h0 ts s.length
      = hexJordan_vertexPos a h0 ts (s.length + 6) := by
    unfold hexJordan_vertexPos
    rw [hk1, hk2, hexJordan_midAccum_append, hexJordan_headAccum_append,
      hexJordan_midAccum_six_right]
    have hh : hexInfra_headAccum (hexInfra_headAccum h0 s) [(-1 : ℤ), -1, -1, -1, -1, -1]
        = hexInfra_headAccum h0 s - 6 := by
      simp only [hexInfra_headAccum_cons, hexInfra_headAccum_nil]; ring
    rw [hh, show hexInfra_headAccum h0 s - 6 = (hexInfra_headAccum h0 s - 6) from rfl,
      show (hexInfra_headAccum h0 s - 6 : ℤ) = (hexInfra_headAccum h0 s - 6) from rfl]
    rw [show (hexInfra_headAccum h0 s - 6 : ℤ) = (hexInfra_headAccum h0 s - 6) from rfl]
    have : HexWalk.halfStep (hexInfra_headAccum h0 s - 6)
        = HexWalk.halfStep (hexInfra_headAccum h0 s) := by
      rw [show (hexInfra_headAccum h0 s - 6 : ℤ) = (hexInfra_headAccum h0 s - 6) + 6 - 6 from by
        ring]
      rw [show (hexInfra_headAccum h0 s - 6 + 6 - 6 : ℤ) = hexInfra_headAccum h0 s - 6 from by ring]
      have h6 := hexStrip_halfStep_add6 (hexInfra_headAccum h0 s - 6)
      rw [show (hexInfra_headAccum h0 s - 6 + 6 : ℤ) = hexInfra_headAccum h0 s from by ring] at h6
      exact h6.symm
    rw [this]
  have hlen : s.length + 6 ≤ ts.length := by
    rw [hts]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
  exact hexJordan_vertexPos_ne_of_saw a h0 ts hsaw s.length (s.length + 6) (by omega) hlen
    (by omega) hpos















noncomputable def hexJordan_simplyConnected_trivial (a : ℂ) (h0 : ℤ) :
    HexStripSimplyConnected (fun m => m = a) a h0 a where
  H := h0
  w := h0
  hHL := le_refl _
  hHU := by omega
  hh0L := le_refl _
  hh0U := by omega
  wall := by
    intro ts hadm k _hk
    have hnil : ts = [] := hexW1_singleton_admissible_nil a h0 ts hadm
    subst hnil
    have : hexStripWinding_runningHead h0 ([] : List ℤ) k = h0 := by
      unfold hexStripWinding_runningHead; simp
    rw [this]
  attainsWall := by
    intro ts hadm
    have hnil : ts = [] := hexW1_singleton_admissible_nil a h0 ts hadm
    subst hnil
    exact ⟨0, by simp, by unfold hexStripWinding_runningHead; simp⟩
  noFullSweep := by
    intro ts hadm i j _hi _hj heq
    have hnil : ts = [] := hexW1_singleton_admissible_nil a h0 ts hadm
    subst hnil
    exfalso
    have hi0 : hexStripWinding_runningHead h0 ([] : List ℤ) i = h0 := by
      unfold hexStripWinding_runningHead; simp
    have hj0 : hexStripWinding_runningHead h0 ([] : List ℤ) j = h0 := by
      unfold hexStripWinding_runningHead; simp
    rw [hi0, hj0] at heq; omega





theorem hexJordan_simplyConnected_trivial_bound (a : ℂ) (h0 : ℤ) :
    |hexInfra_headAccum h0 ([] : List ℤ) - (hexJordan_simplyConnected_trivial a h0).H| < 6 := by
  refine hexJordan_bound (fun m => m = a) a h0 a (hexJordan_simplyConnected_trivial a h0)
    ([] : List ℤ) ?_
  refine ⟨trivialWalk_isLegalSAW a h0, ?_, trivialWalk_endMid a h0⟩
  intro m hm
  have hmids : (HexWalk.ofTurns a h0 ([] : List ℤ)).mids = [a] := by
    unfold HexWalk.mids HexWalk.ofTurns; simp only [HexWalk.midsAux_nil]
  rw [hmids, List.mem_singleton] at hm; exact hm

end StatMech.Universality
