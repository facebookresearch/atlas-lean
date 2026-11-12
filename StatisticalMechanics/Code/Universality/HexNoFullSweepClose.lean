/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






















































































import Mathlib
import Code.Universality.HexStripBandClose

namespace StatMech.Universality

open HexWalk List Complex
open scoped BigOperators Real












theorem hexSweep_runningHead_eq_of_monotone_up (h0 : ℤ) (ts : List ℤ) (i j : ℕ) (hij : i ≤ j)
    (hmono : ∀ k, i ≤ k → k < j → ts[k]?.getD 0 = 1)
    (hsweep : hexStripWinding_runningHead h0 ts j = hexStripWinding_runningHead h0 ts i + 6) :
    j = i + 6 := by
  
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  clear hij
  have key : ∀ e, e ≤ d →
      hexStripWinding_runningHead h0 ts (i + e) = hexStripWinding_runningHead h0 ts i + e := by
    intro e he
    induction e with
    | zero => simp
    | succ n ih =>
      have hn : n ≤ d := by omega
      have hlt : n < d := by omega
      have hidx : i + n < ts.length := by
        by_contra hge
        rw [not_lt] at hge
        have : ts[i + n]?.getD 0 = 1 := hmono (i + n) (by omega) (by omega)
        rw [List.getElem?_eq_none (by omega)] at this
        simp at this
      have hstep := hexStripWinding_runningHead_succ h0 ts (i + n) hidx
      have hval : ts[i + n] = 1 := by
        have := hmono (i + n) (by omega) (by omega)
        rwa [List.getElem?_eq_getElem hidx, Option.getD_some] at this
      rw [show i + (n + 1) = (i + n) + 1 from by ring, hstep, ih hn, hval]
      push_cast; ring
  have := key d (le_refl d)
  rw [hsweep] at this
  have hd : (d : ℤ) = 6 := by omega
  omega



theorem hexSweep_runningHead_eq_of_monotone_down (h0 : ℤ) (ts : List ℤ) (i j : ℕ) (hij : i ≤ j)
    (hmono : ∀ k, i ≤ k → k < j → ts[k]?.getD 0 = -1)
    (hsweep : hexStripWinding_runningHead h0 ts j = hexStripWinding_runningHead h0 ts i - 6) :
    j = i + 6 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  clear hij
  have key : ∀ e, e ≤ d →
      hexStripWinding_runningHead h0 ts (i + e) = hexStripWinding_runningHead h0 ts i - e := by
    intro e he
    induction e with
    | zero => simp
    | succ n ih =>
      have hn : n ≤ d := by omega
      have hlt : n < d := by omega
      have hidx : i + n < ts.length := by
        by_contra hge
        rw [not_lt] at hge
        have : ts[i + n]?.getD 0 = -1 := hmono (i + n) (by omega) (by omega)
        rw [List.getElem?_eq_none (by omega)] at this
        simp at this
      have hstep := hexStripWinding_runningHead_succ h0 ts (i + n) hidx
      have hval : ts[i + n] = -1 := by
        have := hmono (i + n) (by omega) (by omega)
        rwa [List.getElem?_eq_getElem hidx, Option.getD_some] at this
      rw [show i + (n + 1) = (i + n) + 1 from by ring, hstep, ih hn, hval]
      push_cast; ring
  have := key d (le_refl d)
  rw [hsweep] at this
  have hd : (d : ℤ) = 6 := by omega
  omega



theorem hexSweep_segment_eq_six_left (ts : List ℤ) (i : ℕ) (hlen : i + 6 ≤ ts.length)
    (hmono : ∀ k, i ≤ k → k < i + 6 → ts[k]?.getD 0 = 1) :
    (ts.drop i).take 6 = [(1 : ℤ), 1, 1, 1, 1, 1] := by
  apply List.ext_getElem
  · rw [List.length_take, List.length_drop]; simp; omega
  · intro n h1 h2
    have hn6 : n < 6 := by
      rw [List.length_take, List.length_drop] at h1; omega
    rw [List.getElem_take, List.getElem_drop]
    have hval := hmono (i + n) (by omega) (by omega)
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hval
    rw [hval]
    interval_cases n <;> rfl



theorem hexSweep_segment_eq_six_right (ts : List ℤ) (i : ℕ) (hlen : i + 6 ≤ ts.length)
    (hmono : ∀ k, i ≤ k → k < i + 6 → ts[k]?.getD 0 = -1) :
    (ts.drop i).take 6 = [(-1 : ℤ), -1, -1, -1, -1, -1] := by
  apply List.ext_getElem
  · rw [List.length_take, List.length_drop]; simp; omega
  · intro n h1 h2
    have hn6 : n < 6 := by
      rw [List.length_take, List.length_drop] at h1; omega
    rw [List.getElem_take, List.getElem_drop]
    have hval := hmono (i + n) (by omega) (by omega)
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hval
    rw [hval]
    interval_cases n <;> rfl












theorem hexSweep_vertexPos_eq_of_six_left (a : ℂ) (h0 : ℤ) (ts : List ℤ) (i : ℕ)
    (hlen : i + 6 ≤ ts.length)
    (hmono : ∀ k, i ≤ k → k < i + 6 → ts[k]?.getD 0 = 1) :
    hexJordan_vertexPos a h0 ts i = hexJordan_vertexPos a h0 ts (i + 6) := by
  have hsplit : ts.take (i + 6) = ts.take i ++ [(1 : ℤ), 1, 1, 1, 1, 1] := by
    rw [List.take_add, hexSweep_segment_eq_six_left ts i hlen hmono]
  unfold hexJordan_vertexPos
  rw [hsplit, hexJordan_midAccum_append, hexJordan_headAccum_append,
    hexJordan_midAccum_six_left]
  have hh : hexInfra_headAccum (hexInfra_headAccum h0 (ts.take i)) [(1 : ℤ), 1, 1, 1, 1, 1]
      = hexInfra_headAccum h0 (ts.take i) + 6 := by
    simp only [hexInfra_headAccum_cons, hexInfra_headAccum_nil]; ring
  rw [hh, hexStrip_halfStep_add6]




theorem hexSweep_vertexPos_eq_of_six_right (a : ℂ) (h0 : ℤ) (ts : List ℤ) (i : ℕ)
    (hlen : i + 6 ≤ ts.length)
    (hmono : ∀ k, i ≤ k → k < i + 6 → ts[k]?.getD 0 = -1) :
    hexJordan_vertexPos a h0 ts i = hexJordan_vertexPos a h0 ts (i + 6) := by
  have hsplit : ts.take (i + 6) = ts.take i ++ [(-1 : ℤ), -1, -1, -1, -1, -1] := by
    rw [List.take_add, hexSweep_segment_eq_six_right ts i hlen hmono]
  unfold hexJordan_vertexPos
  rw [hsplit, hexJordan_midAccum_append, hexJordan_headAccum_append,
    hexJordan_midAccum_six_right]
  have hh : hexInfra_headAccum (hexInfra_headAccum h0 (ts.take i)) [(-1 : ℤ), -1, -1, -1, -1, -1]
      = hexInfra_headAccum h0 (ts.take i) - 6 := by
    simp only [hexInfra_headAccum_cons, hexInfra_headAccum_nil]; ring
  rw [hh]
  have h6 := hexStrip_halfStep_add6 (hexInfra_headAccum h0 (ts.take i) - 6)
  rw [show (hexInfra_headAccum h0 (ts.take i) - 6 + 6 : ℤ) = hexInfra_headAccum h0 (ts.take i)
    from by ring] at h6
  rw [h6]





theorem hexSweep_vertexPos_eq_of_monotone_up (a : ℂ) (h0 : ℤ) (ts : List ℤ) (i j : ℕ)
    (hij : i ≤ j) (hj : j ≤ ts.length)
    (hmono : ∀ k, i ≤ k → k < j → ts[k]?.getD 0 = 1)
    (hsweep : hexStripWinding_runningHead h0 ts j = hexStripWinding_runningHead h0 ts i + 6) :
    hexJordan_vertexPos a h0 ts i = hexJordan_vertexPos a h0 ts j := by
  have hj6 : j = i + 6 := hexSweep_runningHead_eq_of_monotone_up h0 ts i j hij hmono hsweep
  subst hj6
  exact hexSweep_vertexPos_eq_of_six_left a h0 ts i hj
    (fun k hk hk' => hmono k hk hk')



theorem hexSweep_vertexPos_eq_of_monotone_down (a : ℂ) (h0 : ℤ) (ts : List ℤ) (i j : ℕ)
    (hij : i ≤ j) (hj : j ≤ ts.length)
    (hmono : ∀ k, i ≤ k → k < j → ts[k]?.getD 0 = -1)
    (hsweep : hexStripWinding_runningHead h0 ts j = hexStripWinding_runningHead h0 ts i - 6) :
    hexJordan_vertexPos a h0 ts i = hexJordan_vertexPos a h0 ts j := by
  have hj6 : j = i + 6 := hexSweep_runningHead_eq_of_monotone_down h0 ts i j hij hmono hsweep
  subst hj6
  exact hexSweep_vertexPos_eq_of_six_right a h0 ts i hj
    (fun k hk hk' => hmono k hk hk')

























structure HexStripSimplyConnectedMonotone (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ) where
  
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
  

  monotoneSweep : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z →
      ∀ p q, p ≤ q → q ≤ ts.length →
        (hexStripWinding_runningHead h0 ts q = hexStripWinding_runningHead h0 ts p + 6 →
          ∀ k, p ≤ k → k < q → ts[k]?.getD 0 = 1)
        ∧ (hexStripWinding_runningHead h0 ts q = hexStripWinding_runningHead h0 ts p - 6 →
          ∀ k, p ≤ k → k < q → ts[k]?.getD 0 = -1)

namespace HexStripSimplyConnectedMonotone

variable {inRegion : ℂ → Prop} {a : ℂ} {h0 : ℤ} {z : ℂ}
  (B : HexStripSimplyConnectedMonotone inRegion a h0 z)

include B in






theorem noFullSweepField (ts : List ℤ)
    (hadm : (HexWalk.ofTurns a h0 ts).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z)
    (i j : ℕ) (hi : i ≤ ts.length) (hj : j ≤ ts.length)
    (hsweep : hexStripWinding_runningHead h0 ts j = hexStripWinding_runningHead h0 ts i + 6) :
    hexJordan_vertexPos a h0 ts i = hexJordan_vertexPos a h0 ts j := by
  rcases le_total i j with hij | hji
  · 
    have hmono := (B.monotoneSweep ts hadm i j hij hj).1 hsweep
    exact hexSweep_vertexPos_eq_of_monotone_up a h0 ts i j hij hj hmono hsweep
  · 
    have hdown : hexStripWinding_runningHead h0 ts i = hexStripWinding_runningHead h0 ts j - 6 := by
      omega
    have hmono := (B.monotoneSweep ts hadm j i hji hi).2 hdown
    exact (hexSweep_vertexPos_eq_of_monotone_down a h0 ts j i hji hi hmono hdown).symm

end HexStripSimplyConnectedMonotone





def hexSweep_toSimplyConnected (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (B : HexStripSimplyConnectedMonotone inRegion a h0 z) :
    HexStripSimplyConnected inRegion a h0 z where
  H := B.H
  w := B.w
  hHL := B.hHL
  hHU := B.hHU
  hh0L := B.hh0L
  hh0U := B.hh0U
  wall := B.wall
  attainsWall := B.attainsWall
  noFullSweep := fun ts hadm i j hi hj hsweep => B.noFullSweepField ts hadm i j hi hj hsweep

@[simp] theorem hexSweep_toSimplyConnected_H (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (B : HexStripSimplyConnectedMonotone inRegion a h0 z) :
    (hexSweep_toSimplyConnected inRegion a h0 z B).H = B.H := rfl

@[simp] theorem hexSweep_toSimplyConnected_w (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (B : HexStripSimplyConnectedMonotone inRegion a h0 z) :
    (hexSweep_toSimplyConnected inRegion a h0 z B).w = B.w := rfl










def hexSweep_toStripBand (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (B : HexStripSimplyConnectedMonotone inRegion a h0 z) :
    HexStripBand inRegion a h0 z :=
  hexJordan_toStripBand inRegion a h0 z (hexSweep_toSimplyConnected inRegion a h0 z B)


def hexSweep_stripWinding (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (B : HexStripSimplyConnectedMonotone inRegion a h0 z) :
    HexStripWinding inRegion a h0 z :=
  hexJordan_stripWinding inRegion a h0 z (hexSweep_toSimplyConnected inRegion a h0 z B)

@[simp] theorem hexSweep_stripWinding_H (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (B : HexStripSimplyConnectedMonotone inRegion a h0 z) :
    (hexSweep_stripWinding inRegion a h0 z B).H = B.H := rfl





theorem hexSweep_bound (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (B : HexStripSimplyConnectedMonotone inRegion a h0 z) (ts : List ℤ)
    (hadm : (HexWalk.ofTurns a h0 ts).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z) :
    |hexInfra_headAccum h0 ts - B.H| < 6 :=
  hexJordan_bound inRegion a h0 z (hexSweep_toSimplyConnected inRegion a h0 z B) ts hadm





def hexSweep_toWindingBound (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (B : HexStripSimplyConnectedMonotone inRegion a h0 z)
    (hsideExit : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW
        ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z →
        hexInfra_midAccum a h0 ts + HexWalk.halfStep (hexInfra_headAccum h0 ts)
          = z + HexWalk.halfStep B.H) :
    HexWindingBound inRegion a h0 z :=
  hexJordan_toWindingBound inRegion a h0 z (hexSweep_toSimplyConnected inRegion a h0 z B) hsideExit















noncomputable def hexSweep_simplyConnected_trivial (a : ℂ) (h0 : ℤ) :
    HexStripSimplyConnectedMonotone (fun m => m = a) a h0 a where
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
  monotoneSweep := by
    intro ts hadm p q _hpq _hq
    have hnil : ts = [] := hexW1_singleton_admissible_nil a h0 ts hadm
    subst hnil
    have hp0 : hexStripWinding_runningHead h0 ([] : List ℤ) p = h0 := by
      unfold hexStripWinding_runningHead; simp
    have hq0 : hexStripWinding_runningHead h0 ([] : List ℤ) q = h0 := by
      unfold hexStripWinding_runningHead; simp
    refine ⟨?_, ?_⟩ <;> intro hsweep <;> (rw [hp0, hq0] at hsweep; omega)




theorem hexSweep_simplyConnected_trivial_bound (a : ℂ) (h0 : ℤ) :
    |hexInfra_headAccum h0 ([] : List ℤ) - (hexSweep_simplyConnected_trivial a h0).H| < 6 := by
  refine hexSweep_bound (fun m => m = a) a h0 a (hexSweep_simplyConnected_trivial a h0)
    ([] : List ℤ) ?_
  refine ⟨trivialWalk_isLegalSAW a h0, ?_, trivialWalk_endMid a h0⟩
  intro m hm
  have hmids : (HexWalk.ofTurns a h0 ([] : List ℤ)).mids = [a] := by
    unfold HexWalk.mids HexWalk.ofTurns; simp only [HexWalk.midsAux_nil]
  rw [hmids, List.mem_singleton] at hm; exact hm




















theorem hexSweep_six_left_not_saw (a : ℂ) (h0 : ℤ) (s r : List ℤ)
    (hsaw : (ofTurns a h0 (s ++ ([(1 : ℤ), 1, 1, 1, 1, 1] ++ r))).IsSAW) : False := by
  set ts := s ++ ([(1 : ℤ), 1, 1, 1, 1, 1] ++ r) with hts
  have hlen : s.length + 6 ≤ ts.length := by
    rw [hts]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
  
  have hdrop : ts.drop s.length = [(1 : ℤ), 1, 1, 1, 1, 1] ++ r := by
    rw [hts, List.drop_append_of_le_length (le_refl _)]; simp
  have hmono : ∀ k, s.length ≤ k → k < s.length + 6 → ts[k]?.getD 0 = 1 := by
    intro k hk hk'
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk
    have hek : ts[s.length + n]? = (ts.drop s.length)[n]? := (List.getElem?_drop).symm
    rw [hek, hdrop]
    have hn6 : n < 6 := by omega
    interval_cases n <;> rfl
  have hpos := hexSweep_vertexPos_eq_of_six_left a h0 ts s.length hlen hmono
  exact hexJordan_vertexPos_ne_of_saw a h0 ts hsaw s.length (s.length + 6) (by omega) hlen
    (by omega) hpos






theorem hexSweep_nonMonotone_revolution_pair (h0 : ℤ) :
    hexStripWinding_runningHead h0 [(1 : ℤ), 1, 1, 1, 1, 1, 1, -1] 8
      = hexStripWinding_runningHead h0 [(1 : ℤ), 1, 1, 1, 1, 1, 1, -1] 0 + 6 := by
  simp [hexStripWinding_runningHead]

end StatMech.Universality
