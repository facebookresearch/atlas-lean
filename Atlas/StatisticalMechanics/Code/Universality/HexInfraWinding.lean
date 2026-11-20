/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






















































import Mathlib
import Code.Universality.HexLattice
import Code.Universality.HexInfraDisplacement

namespace StatMech.Universality

open HexWalk List
open scoped BigOperators Real








theorem hexInfra_headAccum_eq_add_sum (h : ℤ) (ts : List ℤ) :
    hexInfra_headAccum h ts = h + ts.sum := by
  induction ts generalizing h with
  | nil => simp
  | cons t ts ih => rw [hexInfra_headAccum_cons, ih, List.sum_cons]; ring





theorem hexInfra_turning_eq_headAccum_sub (a : ℂ) (h0 : ℤ) (ts : List ℤ) :
    (HexWalk.ofTurns a h0 ts).turning
      = (Real.pi / 3) * ((hexInfra_headAccum h0 ts : ℝ) - (h0 : ℝ)) := by
  rw [HexWalk.turning_eq, hexInfra_headAccum_eq_add_sum]
  simp only [HexWalk.ofTurns_turns]
  push_cast; ring



theorem hexInfra_turning_const_of_finalHeading (a : ℂ) (h0 : ℤ) (ts : List ℤ) (H : ℤ)
    (hH : hexInfra_headAccum h0 ts = H) :
    (HexWalk.ofTurns a h0 ts).turning = (Real.pi / 3) * ((H : ℝ) - (h0 : ℝ)) := by
  rw [hexInfra_turning_eq_headAccum_sub, hH]



theorem hexInfra_turning_eq_of_finalHeading_eq (a a' : ℂ) (h0 : ℤ) (ts ts' : List ℤ)
    (hh : hexInfra_headAccum h0 ts = hexInfra_headAccum h0 ts') :
    (HexWalk.ofTurns a h0 ts).turning = (HexWalk.ofTurns a' h0 ts').turning := by
  rw [hexInfra_turning_eq_headAccum_sub, hexInfra_turning_eq_headAccum_sub, hh]







theorem hexInfra_midsAux_getLast? (m : ℂ) (h : ℤ) (ts : List ℤ) :
    (HexWalk.midsAux m h ts).getLast? = some (hexInfra_midAccum m h ts) := by
  induction ts generalizing m h with
  | nil => simp [HexWalk.midsAux]
  | cons t ts ih =>
    rw [HexWalk.midsAux_cons, List.getLast?_cons, ih]
    simp




theorem hexInfra_endMid_eq_midAccum (a : ℂ) (h0 : ℤ) (ts : List ℤ) :
    (HexWalk.ofTurns a h0 ts).endMid = hexInfra_midAccum a h0 ts := by
  unfold HexWalk.endMid HexWalk.mids HexWalk.ofTurns
  have h := List.getLast?_eq_some_getLast
    (show HexWalk.midsAux a h0 ts ≠ [] by cases ts <;> simp [HexWalk.midsAux])
  rw [hexInfra_midsAux_getLast?] at h
  exact (Option.some.inj h).symm




















theorem hexInfra_det_winding_of_finalHeading (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ)
    (z : ℂ) (H : ℤ)
    (hfh : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW
        ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z
        → hexInfra_headAccum h0 ts = H) :
    ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW
        ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z
      → (HexWalk.ofTurns a h0 ts).turning = (Real.pi / 3) * ((H : ℝ) - (h0 : ℝ)) :=
  fun ts hts => hexInfra_turning_const_of_finalHeading a h0 ts H (hfh ts hts)










theorem hexInfra_topSide_finalHeading_zero (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hH : hexInfra_headAccum h0 ts = h0) :
    (HexWalk.ofTurns a h0 ts).turning = 0 := by
  rw [hexInfra_turning_const_of_finalHeading a h0 ts h0 hH]; ring



theorem hexInfra_trivial_finalHeading (h0 : ℤ) :
    hexInfra_headAccum h0 ([] : List ℤ) = h0 := rfl




theorem hexInfra_singleRight_finalHeading (h0 : ℤ) :
    hexInfra_headAccum h0 [(-1 : ℤ)] = h0 - 1 := by
  simp [hexInfra_headAccum_cons, hexInfra_headAccum_nil]; ring




theorem hexInfra_singleRight_turning (a : ℂ) (h0 : ℤ) :
    (HexWalk.ofTurns a h0 [(-1 : ℤ)]).turning = -(Real.pi / 3) := by
  rw [hexInfra_turning_const_of_finalHeading a h0 [(-1 : ℤ)] (h0 - 1)
        (hexInfra_singleRight_finalHeading h0)]
  push_cast; ring

end StatMech.Universality
