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
import Code.Universality.HexW1ExitGeom
import Code.Universality.HexW1HeadingWindow

namespace StatMech.Universality

open HexWalk List Complex
open scoped BigOperators Real










def hexStripWinding_runningHead (h0 : ℤ) (ts : List ℤ) (k : ℕ) : ℤ := h0 + (ts.take k).sum


@[simp] theorem hexStripWinding_runningHead_zero (h0 : ℤ) (ts : List ℤ) :
    hexStripWinding_runningHead h0 ts 0 = h0 := by
  unfold hexStripWinding_runningHead; simp


@[simp] theorem hexStripWinding_runningHead_length (h0 : ℤ) (ts : List ℤ) :
    hexStripWinding_runningHead h0 ts ts.length = hexInfra_headAccum h0 ts := by
  unfold hexStripWinding_runningHead
  rw [hexInfra_headAccum_eq_add_sum, List.take_length]



theorem hexStripWinding_runningHead_succ (h0 : ℤ) (ts : List ℤ) (k : ℕ) (hk : k < ts.length) :
    hexStripWinding_runningHead h0 ts (k + 1)
      = hexStripWinding_runningHead h0 ts k + ts[k] := by
  unfold hexStripWinding_runningHead
  rw [List.take_add_one, List.getElem?_eq_getElem hk, List.sum_append]
  simp only [List.sum_cons, List.sum_nil, add_zero, Option.toList_some]
  ring




theorem hexStripWinding_headAccum_sub (h0 H : ℤ) (ts : List ℤ) :
    hexInfra_headAccum h0 ts - H = ts.sum - (H - h0) := by
  rw [hexInfra_headAccum_eq_add_sum]; ring























structure HexStripWinding (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ) where
  
  H : ℤ
  
  w : ℤ
  
  hHL : w ≤ H
  
  hHU : H < w + 6
  

  window : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z →
      ∀ k, k ≤ ts.length →
        w ≤ hexStripWinding_runningHead h0 ts k
          ∧ hexStripWinding_runningHead h0 ts k < w + 6

namespace HexStripWinding

variable {inRegion : ℂ → Prop} {a : ℂ} {h0 : ℤ} {z : ℂ} (S : HexStripWinding inRegion a h0 z)





theorem headAccum_window (ts : List ℤ)
    (hadm : (HexWalk.ofTurns a h0 ts).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z) :
    S.w ≤ hexInfra_headAccum h0 ts ∧ hexInfra_headAccum h0 ts < S.w + 6 := by
  have h := S.window ts hadm ts.length (le_refl _)
  rwa [hexStripWinding_runningHead_length] at h






theorem bound (ts : List ℤ)
    (hadm : (HexWalk.ofTurns a h0 ts).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z) :
    |hexInfra_headAccum h0 ts - S.H| < 6 := by
  obtain ⟨hgL, hgU⟩ := S.headAccum_window ts hadm
  have hHL := S.hHL
  have hHU := S.hHU
  rw [abs_lt]; omega




theorem heading_eq (ts : List ℤ)
    (hadm : (HexWalk.ofTurns a h0 ts).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z)
    (hsideExit : hexInfra_midAccum a h0 ts + HexWalk.halfStep (hexInfra_headAccum h0 ts)
        = z + HexWalk.halfStep S.H) :
    hexInfra_headAccum h0 ts = S.H := by
  have hdvd := hexInfra_finalHeading_mod_of_lastVertex a h0 z S.H ts hadm.2.2 hsideExit
  exact hexW1_heading_eq_of_dvd_six_of_bound h0 S.H ts hdvd (S.bound ts hadm)

end HexStripWinding













def hexStripWinding_toWindingBound (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (S : HexStripWinding inRegion a h0 z)
    (hsideExit : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW
        ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z →
        hexInfra_midAccum a h0 ts + HexWalk.halfStep (hexInfra_headAccum h0 ts)
          = z + HexWalk.halfStep S.H) :
    HexWindingBound inRegion a h0 z where
  H := S.H
  w := S.w
  hHL := S.hHL
  hHU := S.hHU
  sideExit := hsideExit
  bound := fun ts hadm => S.bound ts hadm

@[simp] theorem hexStripWinding_toWindingBound_H (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (S : HexStripWinding inRegion a h0 z) (hsideExit) :
    (hexStripWinding_toWindingBound inRegion a h0 z S hsideExit).H = S.H := rfl

@[simp] theorem hexStripWinding_toWindingBound_w (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (S : HexStripWinding inRegion a h0 z) (hsideExit) :
    (hexStripWinding_toWindingBound inRegion a h0 z S hsideExit).w = S.w := rfl





def hexStripWinding_toBoundarySide (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (S : HexStripWinding inRegion a h0 z)
    (hsideExit : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW
        ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z →
        hexInfra_midAccum a h0 ts + HexWalk.halfStep (hexInfra_headAccum h0 ts)
          = z + HexWalk.halfStep S.H) :
    HexBoundarySide inRegion a h0 z :=
  (hexStripWinding_toWindingBound inRegion a h0 z S hsideExit).toBoundarySide

















theorem hexStripWinding_window_of_headingBound (a : ℂ) (h0 : ℤ) (z : ℂ) (w : ℤ)
    (inRegion : ℂ → Prop)
    (hbd : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW
        ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z →
        ∀ k, k ≤ ts.length →
          w ≤ hexStripWinding_runningHead h0 ts k
            ∧ hexStripWinding_runningHead h0 ts k < w + 6) :
    ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW
        ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z →
        ∀ k, k ≤ ts.length →
          w ≤ hexStripWinding_runningHead h0 ts k
            ∧ hexStripWinding_runningHead h0 ts k < w + 6 :=
  hbd







theorem hexStripWinding_no_full_turn {inRegion : ℂ → Prop} {a : ℂ} {h0 : ℤ} {z : ℂ}
    (S : HexStripWinding inRegion a h0 z) (ts : List ℤ)
    (hadm : (HexWalk.ofTurns a h0 ts).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z)
    (j k : ℕ) (hj : j ≤ ts.length) (hk : k ≤ ts.length) :
    hexStripWinding_runningHead h0 ts j ≠ hexStripWinding_runningHead h0 ts k + 6 := by
  obtain ⟨hjL, hjU⟩ := S.window ts hadm j hj
  obtain ⟨hkL, hkU⟩ := S.window ts hadm k hk
  omega













theorem hexStripWinding_sidePhaseLock (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (zt zb : ℂ)
    (σ x W r : ℝ)
    (St : HexStripWinding inRegion a h0 zt) (Sb : HexStripWinding inRegion a h0 zb)
    (hsexT : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW
        ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt zt →
        hexInfra_midAccum a h0 ts + HexWalk.halfStep (hexInfra_headAccum h0 ts)
          = zt + HexWalk.halfStep St.H)
    (hsexB : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW
        ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt zb →
        hexInfra_midAccum a h0 ts + HexWalk.halfStep (hexInfra_headAccum h0 ts)
          = zb + HexWalk.halfStep Sb.H)
    (hWt : (Real.pi / 3) * ((St.H : ℝ) - (h0 : ℝ)) = W)
    (hWb : (Real.pi / 3) * ((Sb.H : ℝ) - (h0 : ℝ)) = -W)
    (hreflt : hexClosed_countObs inRegion a h0 zt x = r)
    (hreflb : hexClosed_countObs inRegion a h0 zb x = r) :
    parafObservable inRegion a h0 zt σ x + parafObservable inRegion a h0 zb σ x
      = ((2 * Real.cos (σ * W) * r : ℝ) : ℂ) :=
  hexW1_windingSidePhaseLock inRegion a h0 zt zb σ x W r
    (hexStripWinding_toWindingBound inRegion a h0 zt St hsexT)
    (hexStripWinding_toWindingBound inRegion a h0 zb Sb hsexB)
    hWt hWb hreflt hreflb
















noncomputable def hexStripWinding_trivial (a : ℂ) (h0 : ℤ) :
    HexStripWinding (fun m => m = a) a h0 a where
  H := h0
  w := h0
  hHL := le_refl _
  hHU := by omega
  window := by
    intro ts hadm k hk
    have hnil : ts = [] := hexW1_singleton_admissible_nil a h0 ts hadm
    subst hnil
    
    have : hexStripWinding_runningHead h0 ([] : List ℤ) k = h0 := by
      unfold hexStripWinding_runningHead; simp
    rw [this]; exact ⟨le_refl _, by omega⟩





theorem hexStripWinding_trivial_bound (a : ℂ) (h0 : ℤ) :
    |hexInfra_headAccum h0 ([] : List ℤ) - (hexStripWinding_trivial a h0).H| < 6 := by
  refine (hexStripWinding_trivial a h0).bound ([] : List ℤ) ?_
  refine ⟨trivialWalk_isLegalSAW a h0, ?_, trivialWalk_endMid a h0⟩
  intro m hm
  have hmids : (HexWalk.ofTurns a h0 ([] : List ℤ)).mids = [a] := by
    unfold HexWalk.mids HexWalk.ofTurns; simp only [HexWalk.midsAux_nil]
  rw [hmids, List.mem_singleton] at hm; exact hm






noncomputable def hexStripWinding_trivialWindingBound (a : ℂ) (h0 : ℤ) :
    HexWindingBound (fun m => m = a) a h0 a :=
  hexStripWinding_toWindingBound (fun m => m = a) a h0 a (hexStripWinding_trivial a h0)
    (by
      intro ts hadm
      have hnil : ts = [] := hexW1_singleton_admissible_nil a h0 ts hadm
      subst hnil
      rw [hexInfra_headAccum_nil]
      exact hexInfra_trivial_lastVertex a h0)















theorem hexStripWinding_window_of_boundedPrefixSum (h0 lo : ℤ) (ts : List ℤ)
    (hps : ∀ k, k ≤ ts.length → lo ≤ (ts.take k).sum ∧ (ts.take k).sum < lo + 6) :
    ∀ k, k ≤ ts.length →
      (h0 + lo) ≤ hexStripWinding_runningHead h0 ts k
        ∧ hexStripWinding_runningHead h0 ts k < (h0 + lo) + 6 := by
  intro k hk
  obtain ⟨hL, hU⟩ := hps k hk
  unfold hexStripWinding_runningHead
  omega




















noncomputable def hexStripWinding_singleRight (a : ℂ) (h0 : ℤ) (inReg : ℂ → Prop)
    (hclass : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW
        ∧ (HexWalk.ofTurns a h0 ts).StaysIn inReg
        ∧ (HexWalk.ofTurns a h0 ts).EndsAt
            (a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1))) → ts = [(-1 : ℤ)]) :
    HexStripWinding inReg a h0
      (a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1))) where
  H := h0 - 1
  w := h0 - 1
  hHL := le_refl _
  hHU := by omega
  window := by
    intro ts hadm k hk
    have hts : ts = [(-1 : ℤ)] := hclass ts hadm
    subst hts
    
    have hbase : (h0 - 1 : ℤ) = h0 + (-1) := by ring
    rw [hbase]
    refine hexStripWinding_window_of_boundedPrefixSum h0 (-1) [(-1 : ℤ)] ?_ k hk
    intro j hj
    simp only [List.length_singleton] at hj
    interval_cases j <;> simp






theorem hexStripWinding_singleRight_bound (a : ℂ) (h0 : ℤ) (inReg : ℂ → Prop)
    (hclass : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW
        ∧ (HexWalk.ofTurns a h0 ts).StaysIn inReg
        ∧ (HexWalk.ofTurns a h0 ts).EndsAt
            (a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1))) → ts = [(-1 : ℤ)])
    (hstay : (HexWalk.ofTurns a h0 [(-1 : ℤ)]).StaysIn inReg) :
    |hexInfra_headAccum h0 [(-1 : ℤ)]
        - (hexStripWinding_singleRight a h0 inReg hclass).H| < 6 :=
  (hexStripWinding_singleRight a h0 inReg hclass).bound [(-1 : ℤ)]
    ⟨hexW1Exit_singleRight_legal a h0, hstay, hexW1Exit_singleRight_endsAt a h0⟩

end StatMech.Universality
