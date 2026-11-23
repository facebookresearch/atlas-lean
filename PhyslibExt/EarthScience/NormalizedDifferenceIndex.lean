/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.Field.Basic

import Mathlib.Tactic.Linarith

/-!
# Remote sensing and radiometric inversion

## i. Overview

For nonnegative corrected reflectances `r₁, r₂` with `r₁ + r₂ > 0`, the normalized difference index
  `(r₁ - r₂) / (r₁ + r₂)` (e.g. NDVI) lies in `[-1, 1]`, with endpoints `+1` and `-1` when one band
  vanishes. No retrieval or atmospheric-calibration correctness is claimed; negative calibrated
  samples are outside the hypotheses.

## ii. Key results

- `EarthScience.normalized_difference_index_mem`: the index lies in `[-1, 1]`.
- `EarthScience.normalized_difference_index_eq_one`: endpoint `+1`.
- `EarthScience.normalized_difference_index_eq_neg_one`: endpoint `-1`.

## iii. Table of contents

- A. Normalized difference index range

## iv. References

- `le_div_iff₀`, `div_le_iff₀` in Mathlib.
-/

@[expose] public section

namespace EarthScience

/-- Normalized difference index (e.g. NDVI) range: for nonnegative
reflectances `r₁, r₂` with `r₁ + r₂ > 0`, `(r₁ - r₂) / (r₁ + r₂) ∈ [-1, 1]`. -/
theorem normalized_difference_index_mem {r₁ r₂ : ℝ} (h₁ : 0 ≤ r₁) (h₂ : 0 ≤ r₂)
    (hsum : 0 < r₁ + r₂) :
    -1 ≤ (r₁ - r₂) / (r₁ + r₂) ∧ (r₁ - r₂) / (r₁ + r₂) ≤ 1 := by
  constructor
  · rw [le_div_iff₀ hsum]
    linarith
  · rw [div_le_iff₀ hsum]
    linarith

/-- Endpoint `+1`: no second-band signal and positive first-band signal. -/
theorem normalized_difference_index_eq_one {r₁ : ℝ} (h₁ : 0 < r₁) :
    (r₁ - 0) / (r₁ + 0) = 1 := by
  rw [sub_zero, add_zero]
  exact div_self (ne_of_gt h₁)

/-- Endpoint `-1`: no first-band signal and positive second-band signal. -/
theorem normalized_difference_index_eq_neg_one {r₂ : ℝ} (h₂ : 0 < r₂) :
    (0 - r₂) / (0 + r₂) = -1 := by
  rw [zero_sub, zero_add]
  exact neg_div_self (ne_of_gt h₂)

end EarthScience
