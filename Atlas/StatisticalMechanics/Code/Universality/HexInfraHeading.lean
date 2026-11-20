/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
























































































import Mathlib
import Code.Universality.HexLattice
import Code.Universality.HexInfraDisplacement
import Code.Universality.HexInfraWinding

namespace StatMech.Universality

open HexWalk List Complex
open scoped BigOperators Real








theorem hexUnit_add_six (h : ℤ) : hexUnit (h + 6) = hexUnit h := by
  unfold hexUnit
  have hsplit : Complex.I * (Real.pi / 6 + ((h + 6 : ℤ) : ℝ) * (Real.pi / 3))
      = Complex.I * (Real.pi / 6 + (h : ℝ) * (Real.pi / 3))
        + ((Real.pi : ℂ) * Complex.I + (Real.pi : ℂ) * Complex.I) := by
    push_cast; ring
  rw [hsplit, Complex.exp_add, Complex.exp_add, Complex.exp_pi_mul_I]
  ring




theorem hexUnit_eq_iff_mod (h h' : ℤ) : hexUnit h = hexUnit h' ↔ (6 : ℤ) ∣ (h - h') := by
  unfold hexUnit
  rw [Complex.exp_eq_exp_iff_exists_int]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have key : ((h : ℂ) - (h' : ℂ)) * (Real.pi / 3) = (n : ℂ) * (2 * Real.pi) := by
      have h1 : Complex.I * ((h : ℂ) * (Real.pi / 3) - (h' : ℂ) * (Real.pi / 3)
          - (n : ℂ) * (2 * Real.pi)) = 0 := by linear_combination hn
      have h2 : (h : ℂ) * (Real.pi / 3) - (h' : ℂ) * (Real.pi / 3)
          - (n : ℂ) * (2 * Real.pi) = 0 := by
        rcases mul_eq_zero.mp h1 with hI | hr
        · exact absurd hI Complex.I_ne_zero
        · exact hr
      linear_combination h2
    field_simp at key
    have hcast : (((h - h' : ℤ)) : ℂ) = ((6 * n : ℤ) : ℂ) := by push_cast; linear_combination key
    have := (Int.cast_injective (α := ℂ)) hcast
    omega
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hc : (h : ℂ) - (h' : ℂ) = 6 * (n : ℂ) := by
      have hcast : ((h - h' : ℤ) : ℂ) = ((6 * n : ℤ) : ℂ) := by rw [hn]
      push_cast at hcast; linear_combination hcast
    push_cast
    linear_combination Complex.I * (Real.pi / 3) * hc



theorem hexInfra_halfStep_inj {h h' : ℤ} (he : HexWalk.halfStep h = HexWalk.halfStep h') :
    hexUnit h = hexUnit h' := by
  unfold HexWalk.halfStep at he
  exact mul_left_cancel₀ (by norm_num : (1 / 2 : ℂ) ≠ 0) he











theorem hexInfra_lastVertex_eq_endMid_add (a : ℂ) (h0 : ℤ) (ts : List ℤ) :
    hexInfra_midAccum a h0 ts + HexWalk.halfStep (hexInfra_headAccum h0 ts)
      = (HexWalk.ofTurns a h0 ts).endMid + HexWalk.halfStep (hexInfra_headAccum h0 ts) := by
  rw [hexInfra_endMid_eq_midAccum]




theorem hexInfra_lastVertex_sub_endMid (a : ℂ) (h0 : ℤ) (z : ℂ) (ts : List ℤ)
    (hz : (HexWalk.ofTurns a h0 ts).EndsAt z) :
    (hexInfra_midAccum a h0 ts + HexWalk.halfStep (hexInfra_headAccum h0 ts)) - z
      = HexWalk.halfStep (hexInfra_headAccum h0 ts) := by
  have hzm : hexInfra_midAccum a h0 ts = z := by
    rw [← hexInfra_endMid_eq_midAccum]; exact hz
  rw [hzm]; ring















theorem hexInfra_finalHeading_mod_of_lastVertex (a : ℂ) (h0 : ℤ) (z : ℂ) (H : ℤ) (ts : List ℤ)
    (hz : (HexWalk.ofTurns a h0 ts).EndsAt z)
    (hv : hexInfra_midAccum a h0 ts + HexWalk.halfStep (hexInfra_headAccum h0 ts)
            = z + HexWalk.halfStep H) :
    (6 : ℤ) ∣ (hexInfra_headAccum h0 ts - H) := by
  have hstep : HexWalk.halfStep (hexInfra_headAccum h0 ts) = HexWalk.halfStep H := by
    have hsub := hexInfra_lastVertex_sub_endMid a h0 z ts hz
    have : z + HexWalk.halfStep H - z = HexWalk.halfStep (hexInfra_headAccum h0 ts) := by
      rw [← hv]; exact hsub
    linear_combination -this
  exact (hexUnit_eq_iff_mod _ _).mp (hexInfra_halfStep_inj hstep)











theorem hexInfra_finalHeading_eq_of_lastVertex_of_range (a : ℂ) (h0 : ℤ) (z : ℂ) (H w : ℤ)
    (ts : List ℤ)
    (hz : (HexWalk.ofTurns a h0 ts).EndsAt z)
    (hv : hexInfra_midAccum a h0 ts + HexWalk.halfStep (hexInfra_headAccum h0 ts)
            = z + HexWalk.halfStep H)
    (hwinL : w ≤ hexInfra_headAccum h0 ts) (hwinU : hexInfra_headAccum h0 ts < w + 6)
    (hHL : w ≤ H) (hHU : H < w + 6) :
    hexInfra_headAccum h0 ts = H := by
  have hdvd := hexInfra_finalHeading_mod_of_lastVertex a h0 z H ts hz hv
  omega



















theorem hexInfra_det_winding_of_directedHalfEdge (a : ℂ) (h0 : ℤ) (z : ℂ) (H w : ℤ)
    (ts : List ℤ)
    (hz : (HexWalk.ofTurns a h0 ts).EndsAt z)
    (hv : hexInfra_midAccum a h0 ts + HexWalk.halfStep (hexInfra_headAccum h0 ts)
            = z + HexWalk.halfStep H)
    (hwinL : w ≤ hexInfra_headAccum h0 ts) (hwinU : hexInfra_headAccum h0 ts < w + 6)
    (hHL : w ≤ H) (hHU : H < w + 6) :
    (HexWalk.ofTurns a h0 ts).turning = (Real.pi / 3) * ((H : ℝ) - (h0 : ℝ)) :=
  hexInfra_turning_const_of_finalHeading a h0 ts H
    (hexInfra_finalHeading_eq_of_lastVertex_of_range a h0 z H w ts hz hv hwinL hwinU hHL hHU)









theorem hexInfra_trivial_lastVertex (a : ℂ) (h0 : ℤ) :
    hexInfra_midAccum a h0 ([] : List ℤ) + HexWalk.halfStep (hexInfra_headAccum h0 [])
      = a + HexWalk.halfStep h0 := by
  simp [hexInfra_midAccum_nil, hexInfra_headAccum_nil]





theorem hexInfra_trivial_directedHalfEdge_heading (a : ℂ) (h0 : ℤ) :
    hexInfra_headAccum h0 ([] : List ℤ) = h0 :=
  hexInfra_finalHeading_eq_of_lastVertex_of_range a h0 a h0 h0 ([] : List ℤ)
    (show (HexWalk.ofTurns a h0 []).endMid = a from trivialWalk_endMid a h0)
    (hexInfra_trivial_lastVertex a h0)
    (le_refl _) (by rw [hexInfra_headAccum_nil]; omega)
    (le_refl _) (by omega)





theorem hexInfra_trivial_directedHalfEdge_turning (a : ℂ) (h0 : ℤ) :
    (HexWalk.ofTurns a h0 ([] : List ℤ)).turning = 0 := by
  rw [hexInfra_det_winding_of_directedHalfEdge a h0 a h0 h0 ([] : List ℤ)
        (show (HexWalk.ofTurns a h0 []).endMid = a from trivialWalk_endMid a h0)
        (hexInfra_trivial_lastVertex a h0)
        (le_refl _) (by rw [hexInfra_headAccum_nil]; omega) (le_refl _) (by omega)]
  ring





theorem hexInfra_singleRight_finalHeading_mod :
    (6 : ℤ) ∣ (hexInfra_headAccum 0 [(-1 : ℤ)] - (-1)) := by
  rw [hexInfra_singleRight_finalHeading 0]; norm_num

end StatMech.Universality
