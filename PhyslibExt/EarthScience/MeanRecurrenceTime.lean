/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Mean recurrence time: the return period `T = 1 / p`

If each year independently exceeds a flood level with annual exceedance
probability `p`, the first exceedance year `W` is 1-indexed with
`P(W = n + 1) = p * (1 - p) ^ n`. Its expectation is `1 / p`: the return
period `T = 1 / p` is this mean recurrence time. It is a mean, not a
schedule: a 100-year flood is not guaranteed once per century, and serial
dependence would break the geometric waiting-time law.

## i. Overview

Two routes to the same value: the expectation sum over the
first-exceedance distribution, and the survival-function sum
`E[W] = ∑' n, P(W > n)` with `P(W > n) = (1 - p) ^ n` (the no-exceedance
probability of `PhyslibExt.EarthScience.FloodFrequency`).

## ii. Key results

- `EarthScience.mean_recurrence_time_eq_inv_exceedance_prob`: the
  expectation of the first exceedance year is `1 / p`.
- `EarthScience.mean_recurrence_survival_sum`: the survival sum is `1 / p`.
- `EarthScience.mean_recurrence_hundred_year`: the 100-year flood
  (`p = 0.01`) has mean recurrence time `100` years.

## iii. Table of contents

- A. Mean recurrence time

## iv. References

- `tsum_geometric_of_lt_one`, `tsum_coe_mul_geometric_of_norm_lt_one`
  (Mathlib).

## A. Mean recurrence time
-/

@[expose] public section

namespace EarthScience

/-- No-exceedance geometric sum used by both mean-recurrence theorems. -/
private theorem survival_sum_aux {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ∑' n : ℕ, (1 - p) ^ n = 1 / p := by
  have h0 : (0 : ℝ) ≤ 1 - p := by linarith
  have h1 : (1 : ℝ) - p < 1 := by linarith
  have h := tsum_geometric_of_lt_one h0 h1
  have hrw : (1 : ℝ) - (1 - p) = p := by ring
  rw [hrw, ← one_div] at h
  exact h

/-- Mean recurrence time: if each year independently exceeds with probability `p`,
the first exceedance year `W` (1-indexed) has `P(W = n + 1) = p * (1 - p) ^ n`,
so `E[W] = ∑' n, (n + 1) * (p * (1 - p) ^ n)`. The claim is that this equals
`1 / p`: the return period `T = 1 / p` is the mean recurrence time, not a schedule. -/
theorem mean_recurrence_time_eq_inv_exceedance_prob {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ∑' n : ℕ, ((n : ℝ) + 1) * (p * (1 - p) ^ n) = 1 / p := by
  have h0 : (0 : ℝ) ≤ 1 - p := by linarith
  have h1 : (1 : ℝ) - p < 1 := by linarith
  have hp : p ≠ 0 := ne_of_gt hp0
  have hnorm : ‖(1 - p : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    linarith
  have hgeom : ∑' n : ℕ, (n : ℝ) * (1 - p) ^ n = (1 - p) / (1 - (1 - p)) ^ 2 :=
    tsum_coe_mul_geometric_of_norm_lt_one hnorm
  have hsurv : ∑' n : ℕ, (1 - p) ^ n = 1 / p := survival_sum_aux hp0 hp1
  have hsum1 : Summable (fun n : ℕ => (n : ℝ) * (1 - p) ^ n) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).summable
  have hsum2 : Summable (fun n : ℕ => (1 - p) ^ n) :=
    summable_geometric_of_lt_one h0 h1
  have hcongr : ∀ n : ℕ, ((n : ℝ) + 1) * (p * (1 - p) ^ n)
      = p * ((n : ℝ) * (1 - p) ^ n + (1 - p) ^ n) := fun n => by ring
  rw [tsum_congr hcongr, tsum_mul_left, Summable.tsum_add hsum1 hsum2, hgeom, hsurv]
  have hrw : (1 : ℝ) - (1 - p) = p := by ring
  rw [hrw]
  field_simp
  ring

/-- Survival-function form of the same fact: `P(W > n) = (1 - p) ^ n` is the
parent module's no-exceedance probability, and `E[W] = ∑' n, P(W > n)`. -/
theorem mean_recurrence_survival_sum {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ∑' n : ℕ, (1 - p) ^ n = 1 / p := by
  exact survival_sum_aux hp0 hp1

/-- The 100-year flood: `p = 0.01` has mean recurrence time `100` years. -/
theorem mean_recurrence_hundred_year :
    ∑' n : ℕ, ((n : ℝ) + 1) * ((0.01 : ℝ) * (1 - 0.01) ^ n) = 100 := by
  have h := mean_recurrence_time_eq_inv_exceedance_prob (p := (0.01 : ℝ)) (by norm_num) (by norm_num)
  have h100 : (1 : ℝ) / 0.01 = 100 := by norm_num
  rw [h100] at h
  exact h

end EarthScience
