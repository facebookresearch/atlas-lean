/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


































































































import Mathlib
import Code.Universality.HexStripWinding

namespace StatMech.Universality

open HexWalk List Complex
open scoped BigOperators Real











theorem hexUmlauf_runningHead_step_le (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hlegal : (HexWalk.ofTurns a h0 ts).IsLegalSAW) (k : ℕ) (hk : k < ts.length) :
    |hexStripWinding_runningHead h0 ts (k + 1) - hexStripWinding_runningHead h0 ts k| ≤ 1 := by
  rw [hexStripWinding_runningHead_succ h0 ts k hk]
  have hmem : ts[k] ∈ ts := List.getElem_mem hk
  have hpm : ts[k] = 1 ∨ ts[k] = -1 :=
    hlegal.1 ts[k] (by rw [HexWalk.ofTurns_turns]; exact hmem)
  rcases hpm with h | h <;>
    rw [show hexStripWinding_runningHead h0 ts k + ts[k]
          - hexStripWinding_runningHead h0 ts k = ts[k] from by ring, h] <;>
    decide












theorem hexUmlauf_runningHead_IVT (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hlegal : (HexWalk.ofTurns a h0 ts).IsLegalSAW) :
    ∀ i j : ℕ, i ≤ j → j ≤ ts.length → ∀ m : ℤ,
      min (hexStripWinding_runningHead h0 ts i) (hexStripWinding_runningHead h0 ts j) ≤ m →
      m ≤ max (hexStripWinding_runningHead h0 ts i) (hexStripWinding_runningHead h0 ts j) →
      ∃ c, i ≤ c ∧ c ≤ j ∧ hexStripWinding_runningHead h0 ts c = m := by
  
  set f := fun k => hexStripWinding_runningHead h0 ts k with hf
  intro i j hij hjlen
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  clear hij
  induction d generalizing i with
  | zero =>
    intro m hlo hhi
    simp only [add_zero, min_self, max_self] at hlo hhi
    exact ⟨i, le_refl _, le_refl _, le_antisymm hlo hhi⟩
  | succ d ih =>
    intro m hlo hhi
    by_cases hcase : min (f i) (f (i + d)) ≤ m ∧ m ≤ max (f i) (f (i + d))
    · obtain ⟨c, hci, hcd, hcm⟩ := ih i (by omega) m hcase.1 hcase.2
      exact ⟨c, hci, by omega, hcm⟩
    · 
      
      have hidlt : i + d < ts.length := by omega
      have hs : |f (i + (d + 1)) - f (i + d)| ≤ 1 := by
        have hstep := hexUmlauf_runningHead_step_le a h0 ts hlegal (i + d) hidlt
        have e1 : i + d + 1 = i + (d + 1) := by ring
        rw [e1] at hstep
        exact hstep
      refine ⟨i + (d + 1), by omega, le_refl _, ?_⟩
      change f (i + (d + 1)) = m
      rw [abs_le] at hs
      rw [not_and_or, not_le, not_le] at hcase
      have hmm := min_choice (f i) (f (i + d))
      have hMM := max_choice (f i) (f (i + d))
      have hmm' := min_choice (f i) (f (i + (d + 1)))
      have hMM' := max_choice (f i) (f (i + (d + 1)))
      rcases hmm with h | h <;> rcases hMM with h2 | h2 <;>
        rcases hmm' with h3 | h3 <;> rcases hMM' with h4 | h4 <;>
        rw [h] at hcase <;> rw [h2] at hcase <;> rw [h3] at hlo <;> rw [h4] at hhi <;>
        omega

























theorem hexUmlauf_window_of_wall_noFullTurn (a : ℂ) (h0 : ℤ) (ts : List ℤ) (w : ℤ)
    (hlegal : (HexWalk.ofTurns a h0 ts).IsLegalSAW)
    (hwall : ∀ k, k ≤ ts.length → w ≤ hexStripWinding_runningHead h0 ts k)
    (hnofull : ∀ k, k ≤ ts.length → hexStripWinding_runningHead h0 ts k ≠ w + 6)
    (hanchor : hexStripWinding_runningHead h0 ts 0 < w + 6) :
    ∀ k, k ≤ ts.length →
      w ≤ hexStripWinding_runningHead h0 ts k
        ∧ hexStripWinding_runningHead h0 ts k < w + 6 := by
  intro k hk
  refine ⟨hwall k hk, ?_⟩
  by_contra hge
  rw [not_lt] at hge
  set f := fun n => hexStripWinding_runningHead h0 ts n with hf
  have hf0 : f 0 < w + 6 := hanchor
  have hfk : w + 6 ≤ f k := hge
  
  have hm1 : min (f 0) (f k) ≤ w + 6 := by
    rcases le_total (f 0) (f k) with h | h
    · rw [min_eq_left h]; omega
    · rw [min_eq_right h]; omega
  have hm2 : w + 6 ≤ max (f 0) (f k) := by
    rcases le_total (f 0) (f k) with h | h
    · rw [max_eq_right h]; omega
    · rw [max_eq_left h]; omega
  obtain ⟨c, _hc0, hck, hcm⟩ :=
    hexUmlauf_runningHead_IVT a h0 ts hlegal 0 k (Nat.zero_le k) hk (w + 6) hm1 hm2
  exact hnofull c (by omega) hcm























structure HexStripBand (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ) where
  
  H : ℤ
  
  w : ℤ
  
  hHL : w ≤ H
  
  hHU : H < w + 6
  

  hh0L : w ≤ h0
  

  hh0U : h0 < w + 6
  

  wall : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z →
      ∀ k, k ≤ ts.length → w ≤ hexStripWinding_runningHead h0 ts k
  

  noFullTurn : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z →
      ∀ k, k ≤ ts.length → hexStripWinding_runningHead h0 ts k ≠ w + 6

namespace HexStripBand

variable {inRegion : ℂ → Prop} {a : ℂ} {h0 : ℤ} {z : ℂ} (B : HexStripBand inRegion a h0 z)






theorem windowField (ts : List ℤ)
    (hadm : (HexWalk.ofTurns a h0 ts).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z)
    (k : ℕ) (hk : k ≤ ts.length) :
    B.w ≤ hexStripWinding_runningHead h0 ts k
      ∧ hexStripWinding_runningHead h0 ts k < B.w + 6 := by
  refine hexUmlauf_window_of_wall_noFullTurn a h0 ts B.w hadm.1
    (B.wall ts hadm) (B.noFullTurn ts hadm) ?_ k hk
  
  rw [hexStripWinding_runningHead_zero]; exact B.hh0U

end HexStripBand







def hexUmlauf_stripWinding_of_band (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (B : HexStripBand inRegion a h0 z) :
    HexStripWinding inRegion a h0 z where
  H := B.H
  w := B.w
  hHL := B.hHL
  hHU := B.hHU
  window := fun ts hadm k hk => B.windowField ts hadm k hk

@[simp] theorem hexUmlauf_stripWinding_of_band_H (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (B : HexStripBand inRegion a h0 z) :
    (hexUmlauf_stripWinding_of_band inRegion a h0 z B).H = B.H := rfl

@[simp] theorem hexUmlauf_stripWinding_of_band_w (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (B : HexStripBand inRegion a h0 z) :
    (hexUmlauf_stripWinding_of_band inRegion a h0 z B).w = B.w := rfl





theorem hexUmlauf_bound_of_band (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (B : HexStripBand inRegion a h0 z) (ts : List ℤ)
    (hadm : (HexWalk.ofTurns a h0 ts).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z) :
    |hexInfra_headAccum h0 ts - B.H| < 6 :=
  (hexUmlauf_stripWinding_of_band inRegion a h0 z B).bound ts hadm






def hexUmlauf_band_toWindingBound (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (B : HexStripBand inRegion a h0 z)
    (hsideExit : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW
        ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z →
        hexInfra_midAccum a h0 ts + HexWalk.halfStep (hexInfra_headAccum h0 ts)
          = z + HexWalk.halfStep B.H) :
    HexWindingBound inRegion a h0 z :=
  hexStripWinding_toWindingBound inRegion a h0 z (hexUmlauf_stripWinding_of_band inRegion a h0 z B)
    hsideExit














noncomputable def hexUmlauf_band_trivial (a : ℂ) (h0 : ℤ) :
    HexStripBand (fun m => m = a) a h0 a where
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
  noFullTurn := by
    intro ts hadm k _hk
    have hnil : ts = [] := hexW1_singleton_admissible_nil a h0 ts hadm
    subst hnil
    have : hexStripWinding_runningHead h0 ([] : List ℤ) k = h0 := by
      unfold hexStripWinding_runningHead; simp
    rw [this]; omega





theorem hexUmlauf_band_trivial_bound (a : ℂ) (h0 : ℤ) :
    |hexInfra_headAccum h0 ([] : List ℤ) - (hexUmlauf_band_trivial a h0).H| < 6 := by
  refine hexUmlauf_bound_of_band (fun m => m = a) a h0 a (hexUmlauf_band_trivial a h0)
    ([] : List ℤ) ?_
  refine ⟨trivialWalk_isLegalSAW a h0, ?_, trivialWalk_endMid a h0⟩
  intro m hm
  have hmids : (HexWalk.ofTurns a h0 ([] : List ℤ)).mids = [a] := by
    unfold HexWalk.mids HexWalk.ofTurns; simp only [HexWalk.midsAux_nil]
  rw [hmids, List.mem_singleton] at hm; exact hm

















noncomputable def hexUmlauf_band_singleRight (a : ℂ) (h0 : ℤ) (inReg : ℂ → Prop)
    (hclass : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW
        ∧ (HexWalk.ofTurns a h0 ts).StaysIn inReg
        ∧ (HexWalk.ofTurns a h0 ts).EndsAt
            (a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1))) → ts = [(-1 : ℤ)]) :
    HexStripBand inReg a h0
      (a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1))) where
  H := h0 - 1
  w := h0 - 1
  hHL := le_refl _
  hHU := by omega
  hh0L := by omega
  hh0U := by omega
  wall := by
    intro ts hadm k hk
    have hts : ts = [(-1 : ℤ)] := hclass ts hadm
    subst hts
    simp only [List.length_singleton] at hk
    interval_cases k <;> simp [hexStripWinding_runningHead]
  noFullTurn := by
    intro ts hadm k hk
    have hts : ts = [(-1 : ℤ)] := hclass ts hadm
    subst hts
    simp only [List.length_singleton] at hk
    interval_cases k <;> simp only [hexStripWinding_runningHead] <;> simp <;> omega






theorem hexUmlauf_band_singleRight_bound (a : ℂ) (h0 : ℤ) (inReg : ℂ → Prop)
    (hclass : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW
        ∧ (HexWalk.ofTurns a h0 ts).StaysIn inReg
        ∧ (HexWalk.ofTurns a h0 ts).EndsAt
            (a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1))) → ts = [(-1 : ℤ)])
    (hstay : (HexWalk.ofTurns a h0 [(-1 : ℤ)]).StaysIn inReg) :
    |hexInfra_headAccum h0 [(-1 : ℤ)]
        - (hexUmlauf_band_singleRight a h0 inReg hclass).H| < 6 :=
  hexUmlauf_bound_of_band inReg a h0
    (a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1)))
    (hexUmlauf_band_singleRight a h0 inReg hclass) [(-1 : ℤ)]
    ⟨hexW1Exit_singleRight_legal a h0, hstay, hexW1Exit_singleRight_endsAt a h0⟩













theorem hexUmlauf_no_full_revolution (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (B : HexStripBand inRegion a h0 z) (ts : List ℤ)
    (hadm : (HexWalk.ofTurns a h0 ts).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z)
    (k : ℕ) (hk : k ≤ ts.length) :
    hexStripWinding_runningHead h0 ts k < B.w + 6 :=
  (B.windowField ts hadm k hk).2

end StatMech.Universality
