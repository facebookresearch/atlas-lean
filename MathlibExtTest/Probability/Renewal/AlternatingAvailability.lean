/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Renewal.AlternatingAvailability
import Mathlib.Tactic.NormNum

/-! # Regressions for alternating renewal uptime -/

open Filter MeasureTheory Set Reliability.AlternatingRenewal
open scoped Topology

private theorem cycleEnd_two_one (n : ℕ) :
    cycleEnd (fun _ => 2) (fun _ => 1) n = (n : ℝ) * 3 := by
  norm_num [cycleEnd, Finset.sum_const, nsmul_eq_mul]

-- Two complete up periods and 3/2 time units from the incomplete third period.
example : upTime (fun _ => 2) (fun _ => 1) (15 / 2) = 11 / 2 := by
  unfold upTime
  rw [tsum_eq_sum (s := Finset.range 3)]
  · norm_num [cycleEnd_two_one, Finset.sum_range_succ]
  · intro i hi
    have hi' : 3 ≤ i := Nat.le_of_not_gt (fun h => hi (Finset.mem_range.mpr h))
    have hs : (3 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi'
    rw [cycleEnd_two_one, max_eq_right]
    apply sub_nonpos.mpr
    exact (min_le_left _ _).trans (by linarith)

example : Tendsto (fun t : ℝ => upTime (fun _ => 2) (fun _ => 1) t / t)
    atTop (𝓝 (2 / 3)) := by
  apply tendsto_upTime_div (by norm_num) (by norm_num) (by norm_num)
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    simp [Finset.sum_const, nsmul_eq_mul, hn']
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    simp [cycleEnd_two_one, hn']

-- Zero-duration up phases never contribute, even when the cycle clock advances.
example (D : ℕ → ℝ) (t : ℝ) : upTime (fun _ => 0) D t = 0 := by
  unfold upTime
  have h (i : ℕ) : max (min t (cycleEnd (fun _ => 0) D i + 0) -
      cycleEnd (fun _ => 0) D i) 0 = 0 := by
    rw [add_zero, max_eq_right (sub_nonpos.mpr (min_le_right _ _))]
  simp only [h, tsum_zero]

-- The elapsed up-time is also the length of the union of the clipped up intervals.
example : volume.real (Ico 0 (15 / 2 : ℝ) ∩
    ⋃ i, Ico (cycleEnd (fun _ => 2) (fun _ => 1) i)
      (cycleEnd (fun _ => 2) (fun _ => 1) i + 2)) =
    upTime (fun _ => 2) (fun _ => 1) (15 / 2) := by
  symm
  apply upTime_eq_volume (by norm_num) (by norm_num)
  have h := (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_pos (by norm_num : (0 : ℝ) < 3)
    (tendsto_const_nhds (x := (3 : ℝ)))
  exact h.congr (fun n => (cycleEnd_two_one n).symm)

private def zeroFirstUp (i : ℕ) : ℝ := if i = 0 then 0 else 2
private def zeroFirstDown (i : ℕ) : ℝ := if i = 0 then 0 else 1

private theorem zeroFirstEnd (n : ℕ) :
    cycleEnd zeroFirstUp zeroFirstDown (n + 1) = (n : ℝ) * 3 := by
  induction n with
  | zero => norm_num [cycleEnd, zeroFirstUp, zeroFirstDown]
  | succ n ih =>
    have hs : cycleEnd zeroFirstUp zeroFirstDown (n + 1 + 1) =
        cycleEnd zeroFirstUp zeroFirstDown (n + 1) +
          (zeroFirstUp (n + 1) + zeroFirstDown (n + 1)) := Finset.sum_range_succ _ _
    rw [hs, ih]
    simp [zeroFirstUp, zeroFirstDown, Nat.cast_succ]
    ring

-- The first cycle has length zero; the second starts at the same endpoint and contributes
-- one unit of uptime through time 1.
example : cycleEnd zeroFirstUp zeroFirstDown 0 = cycleEnd zeroFirstUp zeroFirstDown 1 ∧
    upTime zeroFirstUp zeroFirstDown 1 = 1 := by
  constructor
  · norm_num [cycleEnd, zeroFirstUp, zeroFirstDown]
  · unfold upTime
    rw [tsum_eq_sum (s := Finset.range 2)]
    · norm_num [Finset.sum_range_succ, cycleEnd, zeroFirstUp, zeroFirstDown]
    · intro i hi
      have hi' : 2 ≤ i := Nat.le_of_not_gt (fun h => hi (Finset.mem_range.mpr h))
      cases i with
      | zero => omega
      | succ n =>
        have hn : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
        rw [zeroFirstEnd, max_eq_right]
        exact sub_nonpos.mpr ((min_le_left _ _).trans (by linarith))
