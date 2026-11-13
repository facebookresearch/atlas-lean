/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




























































































import Mathlib
import Code.Universality.HexInfraWinding
import Code.Universality.HexInfraHeading
import Code.Universality.HexW1Sides

namespace StatMech.Universality

open HexWalk List Complex
open scoped BigOperators Real













theorem hexW1_heading_eq_of_dvd_six_of_bound (h0 : ℤ) (H : ℤ) (ts : List ℤ)
    (hdvd : (6 : ℤ) ∣ (hexInfra_headAccum h0 ts - H))
    (hbound : |hexInfra_headAccum h0 ts - H| < 6) :
    hexInfra_headAccum h0 ts = H := by
  obtain ⟨k, hk⟩ := hdvd
  rw [hk] at hbound
  rw [abs_lt] at hbound
  have hk0 : k = 0 := by omega
  omega




theorem hexW1_heading_window_of_eq (h0 : ℤ) (H w : ℤ) (ts : List ℤ)
    (heq : hexInfra_headAccum h0 ts = H) (hHL : w ≤ H) (hHU : H < w + 6) :
    w ≤ hexInfra_headAccum h0 ts ∧ hexInfra_headAccum h0 ts < w + 6 := by
  rw [heq]; exact ⟨hHL, hHU⟩






theorem hexW1_bound_does_not_force_eq (H : ℤ) :
    |(H + 3) - H| < 6 ∧ (H + 3) ≠ H := by
  refine ⟨?_, by omega⟩
  rw [show (H + 3) - H = 3 by ring]; decide



























structure HexWindingBound (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ) where
  
  H : ℤ
  
  w : ℤ
  
  hHL : w ≤ H
  
  hHU : H < w + 6
  

  sideExit : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z →
      hexInfra_midAccum a h0 ts + HexWalk.halfStep (hexInfra_headAccum h0 ts)
        = z + HexWalk.halfStep H
  


  bound : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z →
      |hexInfra_headAccum h0 ts - H| < 6

namespace HexWindingBound

variable {inRegion : ℂ → Prop} {a : ℂ} {h0 : ℤ} {z : ℂ} (S : HexWindingBound inRegion a h0 z)





theorem heading_eq (ts : List ℤ)
    (hadm : (HexWalk.ofTurns a h0 ts).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z) :
    hexInfra_headAccum h0 ts = S.H := by
  have hv := S.sideExit ts hadm
  have hdvd := hexInfra_finalHeading_mod_of_lastVertex a h0 z S.H ts hadm.2.2 hv
  exact hexW1_heading_eq_of_dvd_six_of_bound h0 S.H ts hdvd (S.bound ts hadm)






theorem exits : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z →
      (hexInfra_midAccum a h0 ts + HexWalk.halfStep (hexInfra_headAccum h0 ts)
          = z + HexWalk.halfStep S.H)
        ∧ (S.w ≤ hexInfra_headAccum h0 ts ∧ hexInfra_headAccum h0 ts < S.w + 6) := by
  intro ts hadm
  refine ⟨S.sideExit ts hadm, ?_⟩
  exact hexW1_heading_window_of_eq h0 S.H S.w ts (S.heading_eq ts hadm) S.hHL S.hHU






def toBoundarySide : HexBoundarySide inRegion a h0 z where
  H := S.H
  w := S.w
  hHL := S.hHL
  hHU := S.hHU
  exits := S.exits

@[simp] theorem toBoundarySide_H : S.toBoundarySide.H = S.H := rfl
@[simp] theorem toBoundarySide_w : S.toBoundarySide.w = S.w := rfl




theorem turning_const (ts : List ℤ)
    (hadm : (HexWalk.ofTurns a h0 ts).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z) :
    (HexWalk.ofTurns a h0 ts).turning = (Real.pi / 3) * ((S.H : ℝ) - (h0 : ℝ)) :=
  S.toBoundarySide.turning_const ts hadm

end HexWindingBound














theorem hexW1_windingSidePhaseLock (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (zt zb : ℂ)
    (σ x W r : ℝ)
    (Bt : HexWindingBound inRegion a h0 zt) (Bb : HexWindingBound inRegion a h0 zb)
    (hWt : (Real.pi / 3) * ((Bt.H : ℝ) - (h0 : ℝ)) = W)
    (hWb : (Real.pi / 3) * ((Bb.H : ℝ) - (h0 : ℝ)) = -W)
    (hreflt : hexClosed_countObs inRegion a h0 zt x = r)
    (hreflb : hexClosed_countObs inRegion a h0 zb x = r) :
    parafObservable inRegion a h0 zt σ x + parafObservable inRegion a h0 zb σ x
      = ((2 * Real.cos (σ * W) * r : ℝ) : ℂ) :=
  hexW1_sidePhaseLock inRegion a h0 zt zb σ x W r Bt.toBoundarySide Bb.toBoundarySide
    hWt hWb hreflt hreflb

















noncomputable def hexW1_trivialWindingBound (a : ℂ) (h0 : ℤ) :
    HexWindingBound (fun m => m = a) a h0 a where
  H := h0
  w := h0
  hHL := le_refl _
  hHU := by omega
  sideExit := by
    intro ts hadm
    have hnil : ts = [] := hexW1_singleton_admissible_nil a h0 ts hadm
    subst hnil
    rw [hexInfra_headAccum_nil]
    exact hexInfra_trivial_lastVertex a h0
  bound := by
    intro ts hadm
    have hnil : ts = [] := hexW1_singleton_admissible_nil a h0 ts hadm
    subst hnil
    rw [hexInfra_headAccum_nil]
    norm_num





theorem hexW1_trivialWindingBound_toBoundarySide_heading (a : ℂ) (h0 : ℤ) :
    hexInfra_headAccum h0 ([] : List ℤ) = (hexW1_trivialWindingBound a h0).toBoundarySide.H := by
  have hadm : (HexWalk.ofTurns a h0 ([] : List ℤ)).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 ([] : List ℤ)).StaysIn (fun m => m = a)
      ∧ (HexWalk.ofTurns a h0 ([] : List ℤ)).EndsAt a := by
    refine ⟨trivialWalk_isLegalSAW a h0, ?_, trivialWalk_endMid a h0⟩
    intro m hm
    have hmids : (HexWalk.ofTurns a h0 ([] : List ℤ)).mids = [a] := by
      unfold HexWalk.mids HexWalk.ofTurns; simp only [HexWalk.midsAux_nil]
    rw [hmids, List.mem_singleton] at hm; exact hm
  exact (hexW1_trivialWindingBound a h0).toBoundarySide.heading_det ([] : List ℤ) hadm




theorem hexW1_trivialWindingBound_turning_zero (a : ℂ) (h0 : ℤ) :
    (HexWalk.ofTurns a h0 ([] : List ℤ)).turning = 0 := by
  have hadm : (HexWalk.ofTurns a h0 ([] : List ℤ)).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 ([] : List ℤ)).StaysIn (fun m => m = a)
      ∧ (HexWalk.ofTurns a h0 ([] : List ℤ)).EndsAt a := by
    refine ⟨trivialWalk_isLegalSAW a h0, ?_, trivialWalk_endMid a h0⟩
    intro m hm
    have hmids : (HexWalk.ofTurns a h0 ([] : List ℤ)).mids = [a] := by
      unfold HexWalk.mids HexWalk.ofTurns; simp only [HexWalk.midsAux_nil]
    rw [hmids, List.mem_singleton] at hm; exact hm
  have hkey := (hexW1_trivialWindingBound a h0).toBoundarySide.turning_const ([] : List ℤ) hadm
  have hH : (hexW1_trivialWindingBound a h0).toBoundarySide.H = h0 := rfl
  rw [hH] at hkey
  rw [hkey]; ring

end StatMech.Universality
