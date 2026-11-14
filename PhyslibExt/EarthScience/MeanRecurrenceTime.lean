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
# Geometric-series identities behind the return period `T = 1 / p`

For `0 < p ≤ 1`, the series `∑' n, (n + 1) * (p * (1 - p) ^ n)` and
`∑' n, (1 - p) ^ n` both equal `1 / p`. This module proves these two
real-series identities and nothing more.

## i. Overview

Context, not formalized here: in the textbook flood-frequency model each year
exceeds a level independently with annual probability `p`, the first
exceedance year `W` has `P(W = n + 1) = p * (1 - p) ^ n` and
`P(W > n) = (1 - p) ^ n`, and the return period `T = 1 / p` is the mean
`E[W]`, computed by either series above. This module contains no probability
space, yearly events, independence hypothesis, random variable `W` or
expectation, and it does not use `PhyslibExt.EarthScience.FloodFrequency`;
the statements below are identities about real numbers `p ∈ (0, 1]` only.

## ii. Key results

- `EarthScience.weighted_geometric_tsum_eq_inv`:
  `∑' n, (n + 1) * (p * (1 - p) ^ n) = 1 / p`.
- `EarthScience.geometric_tsum_one_sub_eq_inv`: `∑' n, (1 - p) ^ n = 1 / p`,
  the instance `r = 1 - p` of Mathlib's `tsum_geometric_of_lt_one`.
- `EarthScience.weighted_geometric_tsum_one_hundredth`: at `p = 0.01` the
  weighted series is `100`.

## iii. Table of contents

- A. The two series

## iv. References

- `tsum_geometric_of_lt_one`, `tsum_coe_mul_geometric_of_norm_lt_one`
  (Mathlib).

## A. The two series
-/

@[expose] public section

namespace EarthScience

/-- The geometric sum `∑' n, (1 - p) ^ n = 1 / p`, used by both public theorems. -/
private theorem survival_sum_aux {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ∑' n : ℕ, (1 - p) ^ n = 1 / p := by
  have h0 : (0 : ℝ) ≤ 1 - p := by linarith
  have h1 : (1 : ℝ) - p < 1 := by linarith
  have h := tsum_geometric_of_lt_one h0 h1
  have hrw : (1 : ℝ) - (1 - p) = p := by ring
  rw [hrw, ← one_div] at h
  exact h

/-- The weighted geometric series `∑' n, (n + 1) * (p * (1 - p) ^ n)` equals `1 / p` for
`0 < p ≤ 1`. This is a real-series identity: no random variable or expectation appears. In the
flood-frequency model described in the module docstring (not formalized here), the left side is
the mean of the first exceedance year. -/
theorem weighted_geometric_tsum_eq_inv {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
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

/-- The geometric series `∑' n, (1 - p) ^ n` equals `1 / p` for `0 < p ≤ 1`: Mathlib's
`tsum_geometric_of_lt_one` at `r = 1 - p`, with the limit written as `1 / p`. -/
theorem geometric_tsum_one_sub_eq_inv {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ∑' n : ℕ, (1 - p) ^ n = 1 / p := by
  exact survival_sum_aux hp0 hp1

/-- At `p = 0.01` the weighted geometric series is `100`. -/
theorem weighted_geometric_tsum_one_hundredth :
    ∑' n : ℕ, ((n : ℝ) + 1) * ((0.01 : ℝ) * (1 - 0.01) ^ n) = 100 := by
  have h := weighted_geometric_tsum_eq_inv (p := (0.01 : ℝ)) (by norm_num) (by norm_num)
  have h100 : (1 : ℝ) / 0.01 = 100 := by norm_num
  rw [h100] at h
  exact h

end EarthScience
