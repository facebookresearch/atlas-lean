/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


























































































import Mathlib
import Code.Universality.HexInfraWinding
import Code.Universality.HexInfraHeading
import Code.Universality.HexConnClosed

namespace StatMech.Universality

open HexWalk List Complex Filter Topology
open scoped BigOperators Real Topology













theorem hexW1_heading_sub_dvd_six_of_sideExit (a : ℂ) (h0 : ℤ) (z : ℂ) (H : ℤ)
    (ts₁ ts₂ : List ℤ)
    (hz₁ : (HexWalk.ofTurns a h0 ts₁).EndsAt z)
    (hv₁ : hexInfra_midAccum a h0 ts₁ + HexWalk.halfStep (hexInfra_headAccum h0 ts₁)
            = z + HexWalk.halfStep H)
    (hz₂ : (HexWalk.ofTurns a h0 ts₂).EndsAt z)
    (hv₂ : hexInfra_midAccum a h0 ts₂ + HexWalk.halfStep (hexInfra_headAccum h0 ts₂)
            = z + HexWalk.halfStep H) :
    (6 : ℤ) ∣ (hexInfra_headAccum h0 ts₁ - hexInfra_headAccum h0 ts₂) := by
  have h1 := hexInfra_finalHeading_mod_of_lastVertex a h0 z H ts₁ hz₁ hv₁
  have h2 := hexInfra_finalHeading_mod_of_lastVertex a h0 z H ts₂ hz₂ hv₂
  omega






















structure HexBoundarySide (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ) where
  
  H : ℤ
  
  w : ℤ
  
  hHL : w ≤ H
  
  hHU : H < w + 6
  

  exits : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z →
      (hexInfra_midAccum a h0 ts + HexWalk.halfStep (hexInfra_headAccum h0 ts)
          = z + HexWalk.halfStep H)
        ∧ (w ≤ hexInfra_headAccum h0 ts ∧ hexInfra_headAccum h0 ts < w + 6)

namespace HexBoundarySide

variable {inRegion : ℂ → Prop} {a : ℂ} {h0 : ℤ} {z : ℂ} (S : HexBoundarySide inRegion a h0 z)





theorem heading_det (ts : List ℤ)
    (hadm : (HexWalk.ofTurns a h0 ts).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z) :
    hexInfra_headAccum h0 ts = S.H := by
  obtain ⟨hv, hwL, hwU⟩ := S.exits ts hadm
  exact hexInfra_finalHeading_eq_of_lastVertex_of_range a h0 z S.H S.w ts hadm.2.2 hv
    hwL hwU S.hHL S.hHU





theorem turning_const (ts : List ℤ)
    (hadm : (HexWalk.ofTurns a h0 ts).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z) :
    (HexWalk.ofTurns a h0 ts).turning = (Real.pi / 3) * ((S.H : ℝ) - (h0 : ℝ)) :=
  hexInfra_turning_const_of_finalHeading a h0 ts S.H (S.heading_det ts hadm)





theorem hdet : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z
    → (HexWalk.ofTurns a h0 ts).turning = (Real.pi / 3) * ((S.H : ℝ) - (h0 : ℝ)) :=
  fun ts hadm => S.turning_const ts hadm

end HexBoundarySide





















theorem hexW1_sidePhaseLock (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (zt zb : ℂ)
    (σ x W r : ℝ)
    (St : HexBoundarySide inRegion a h0 zt) (Sb : HexBoundarySide inRegion a h0 zb)
    (hWt : (Real.pi / 3) * ((St.H : ℝ) - (h0 : ℝ)) = W)
    (hWb : (Real.pi / 3) * ((Sb.H : ℝ) - (h0 : ℝ)) = -W)
    (hreflt : hexClosed_countObs inRegion a h0 zt x = r)
    (hreflb : hexClosed_countObs inRegion a h0 zb x = r) :
    parafObservable inRegion a h0 zt σ x + parafObservable inRegion a h0 zb σ x
      = ((2 * Real.cos (σ * W) * r : ℝ) : ℂ) := by
  refine hexClosed_sidePhaseLock_of_reflection inRegion a h0 zt zb σ x W r ?_ ?_ hreflt hreflb
  · intro ts hadm; rw [St.turning_const ts hadm, hWt]
  · intro ts hadm; rw [Sb.turning_const ts hadm, hWb]

















theorem hexW1_bottomSide_phaseLock (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (zt zb : ℂ)
    (x r : ℝ)
    (St : HexBoundarySide inRegion a h0 zt) (Sb : HexBoundarySide inRegion a h0 zb)
    (hWt : (Real.pi / 3) * ((St.H : ℝ) - (h0 : ℝ)) = Real.pi)
    (hWb : (Real.pi / 3) * ((Sb.H : ℝ) - (h0 : ℝ)) = -Real.pi)
    (hreflt : hexClosed_countObs inRegion a h0 zt x = r)
    (hreflb : hexClosed_countObs inRegion a h0 zb x = r) :
    parafObservable inRegion a h0 zt (5 / 8) x + parafObservable inRegion a h0 zb (5 / 8) x
      = ((-(2 * hexBdryCl) * r : ℝ) : ℂ) := by
  rw [hexW1_sidePhaseLock inRegion a h0 zt zb (5 / 8) x Real.pi r St Sb hWt hWb hreflt hreflb]
  congr 1
  have : Real.cos ((5 / 8 : ℝ) * Real.pi) = -hexBdryCl := hexClosed_cos_sigmaPi_eq_neg_cl
  rw [this]; ring













theorem hexW1_hexUnit_add_int (h t : ℤ) :
    hexUnit (h + t) = hexUnit h * Complex.exp (Complex.I * ((t : ℝ) * (Real.pi / 3))) := by
  unfold hexUnit; rw [← Complex.exp_add]; congr 1; push_cast; ring




theorem hexW1_halfStep_add_ne_zero (h t : ℤ) (ht : t = 1 ∨ t = -1) :
    HexWalk.halfStep h + HexWalk.halfStep (h + t) ≠ 0 := by
  unfold HexWalk.halfStep
  rw [hexW1_hexUnit_add_int]
  rw [show (1/2 : ℂ) * hexUnit h
        + (1/2 : ℂ) * (hexUnit h * Complex.exp (Complex.I * ((t:ℝ)*(Real.pi/3))))
      = (1/2 : ℂ) * hexUnit h * (1 + Complex.exp (Complex.I * ((t:ℝ)*(Real.pi/3)))) by ring]
  apply mul_ne_zero (mul_ne_zero (by norm_num) (hexUnit_ne_zero h))
  have hre : (1 + Complex.exp (Complex.I * ((t:ℝ) * (Real.pi/3)))).re
      = 1 + Real.cos ((t:ℝ)*(Real.pi/3)) := by
    rw [Complex.add_re, Complex.one_re]; congr 1
    rw [show Complex.I * ((t:ℝ) * (Real.pi/3)) = (((t:ℝ)*(Real.pi/3)) : ℝ) * Complex.I by
        push_cast; ring]
    rw [Complex.exp_ofReal_mul_I_re]
  intro hc
  have h0 : (1 + Complex.exp (Complex.I * ((t:ℝ)*(Real.pi/3)))).re = 0 := by rw [hc]; simp
  rw [hre] at h0
  have hcos : Real.cos ((t:ℝ)*(Real.pi/3)) = 1/2 := by
    rcases ht with rfl | rfl
    · push_cast; rw [show (1:ℝ)*(Real.pi/3) = Real.pi/3 by ring, Real.cos_pi_div_three]
    · push_cast
      rw [show (-1:ℝ)*(Real.pi/3) = -(Real.pi/3) by ring, Real.cos_neg, Real.cos_pi_div_three]
  rw [hcos] at h0; norm_num at h0





theorem hexW1_singleton_admissible_nil (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hadm : (HexWalk.ofTurns a h0 ts).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 ts).StaysIn (fun m => m = a)
      ∧ (HexWalk.ofTurns a h0 ts).EndsAt a) :
    ts = [] := by
  obtain ⟨hlegal, hstay, _⟩ := hadm
  cases ts with
  | nil => rfl
  | cons t ts =>
    exfalso
    have hsecond : a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + t)
        ∈ (HexWalk.ofTurns a h0 (t :: ts)).mids := by
      unfold HexWalk.mids HexWalk.ofTurns
      rw [HexWalk.midsAux_cons]
      refine List.mem_cons_of_mem _ ?_
      cases ts with
      | nil => simp only [HexWalk.midsAux_nil, List.mem_singleton]
      | cons s ss => rw [HexWalk.midsAux_cons]; exact List.mem_cons_self
    have hsa := hstay _ hsecond
    have hzero : HexWalk.halfStep h0 + HexWalk.halfStep (h0 + t) = 0 := by
      have hcalc : a + (HexWalk.halfStep h0 + HexWalk.halfStep (h0 + t)) = a + 0 := by
        rw [add_zero, ← add_assoc]; exact hsa
      exact add_left_cancel hcalc
    have ht : t = 1 ∨ t = -1 := hlegal.1 t (by simp [HexWalk.ofTurns])
    exact hexW1_halfStep_add_ne_zero h0 t ht hzero







noncomputable def hexW1_trivialSide (a : ℂ) (h0 : ℤ) :
    HexBoundarySide (fun m => m = a) a h0 a where
  H := h0
  w := h0
  hHL := le_refl _
  hHU := by omega
  exits := by
    intro ts hadm
    have hnil : ts = [] := hexW1_singleton_admissible_nil a h0 ts hadm
    subst hnil
    rw [hexInfra_headAccum_nil]
    exact ⟨by rw [hexInfra_midAccum_nil], le_refl _, by omega⟩





theorem hexW1_trivialSide_turning_zero (a : ℂ) (h0 : ℤ) :
    (HexWalk.ofTurns a h0 ([] : List ℤ)).turning = 0 := by
  have hadm : (HexWalk.ofTurns a h0 ([] : List ℤ)).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 ([] : List ℤ)).StaysIn (fun m => m = a)
      ∧ (HexWalk.ofTurns a h0 ([] : List ℤ)).EndsAt a := by
    refine ⟨trivialWalk_isLegalSAW a h0, ?_, trivialWalk_endMid a h0⟩
    intro m hm
    have hmids : (HexWalk.ofTurns a h0 ([] : List ℤ)).mids = [a] := by
      unfold HexWalk.mids HexWalk.ofTurns; simp only [HexWalk.midsAux_nil]
    rw [hmids] at hm
    rw [List.mem_singleton] at hm; exact hm
  have hkey := (hexW1_trivialSide a h0).turning_const ([] : List ℤ) hadm
  have hH : (hexW1_trivialSide a h0).H = h0 := rfl
  rw [hH] at hkey
  rw [hkey]; ring

end StatMech.Universality
