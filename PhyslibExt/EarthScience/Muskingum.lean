/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Muskingum routing coefficients

## i. Overview

The Muskingum flood-routing method advances outflow with coefficients
`C0`, `C1`, `C2` built from storage constant `K`, weight `X`, and time
step `dt`, over the denominator `2 * K * (1 - X) + dt`. The coefficients
sum to one, and for `K > 0`, `0 ≤ X ≤ 1 / 2`, `dt > 0` they are all
nonnegative exactly when `2 * K * X ≤ dt ≤ 2 * K * (1 - X)`.

## ii. Key results

- `EarthScience.muskingum_coefficients_sum`: the coefficients sum to one.
- `EarthScience.muskingum_nonneg_iff`: the nonnegative-coefficient
  admissibility window.

## iii. Table of contents

- A. Coefficients and admissibility

## iv. References

- V. T. Chow, D. R. Maidment and L. W. Mays, *Applied Hydrology*,
  McGraw-Hill, 1988 (Muskingum routing).
-/

@[expose] public section

namespace EarthScience

/-! ## A. Coefficients and admissibility -/

/-- Muskingum storage-weighting denominator `2 * K * (1 - X) + dt`. -/
noncomputable def muskingumDenominator (K X dt : ℝ) : ℝ :=
  2 * K * (1 - X) + dt

/-- Muskingum routing coefficient on the current inflow,
`(dt - 2 * K * X) / (2 * K * (1 - X) + dt)`. With the convention `x / 0 = 0` it is `0` when the
denominator vanishes; the intended domain is `K > 0`, `0 ≤ X ≤ 1 / 2`, `dt > 0`. -/
noncomputable def muskingumC0 (K X dt : ℝ) : ℝ :=
  (dt - 2 * K * X) / muskingumDenominator K X dt

/-- Muskingum routing coefficient on the previous inflow,
`(dt + 2 * K * X) / (2 * K * (1 - X) + dt)`. With the convention `x / 0 = 0` it is `0` when the
denominator vanishes; the intended domain is `K > 0`, `0 ≤ X ≤ 1 / 2`, `dt > 0`. -/
noncomputable def muskingumC1 (K X dt : ℝ) : ℝ :=
  (dt + 2 * K * X) / muskingumDenominator K X dt

/-- Muskingum routing coefficient on the previous outflow,
`(2 * K * (1 - X) - dt) / (2 * K * (1 - X) + dt)`. With the convention `x / 0 = 0` it is `0` when
the denominator vanishes; the intended domain is `K > 0`, `0 ≤ X ≤ 1 / 2`, `dt > 0`. -/
noncomputable def muskingumC2 (K X dt : ℝ) : ℝ :=
  (2 * K * (1 - X) - dt) / muskingumDenominator K X dt

/-- The three Muskingum coefficients sum to one when the denominator
`2 * K * (1 - X) + dt` is nonzero. -/
theorem muskingum_coefficients_sum {K X dt : ℝ}
    (hden : muskingumDenominator K X dt ≠ 0) :
    muskingumC0 K X dt + muskingumC1 K X dt + muskingumC2 K X dt = 1 := by
  simp only [muskingumC0, muskingumC1, muskingumC2, muskingumDenominator] at hden ⊢
  field_simp
  ring

/-- For `K > 0`, `0 ≤ X ≤ 1 / 2`, `dt > 0`, all three coefficients are
nonnegative exactly when `2 * K * X ≤ dt ≤ 2 * K * (1 - X)`. -/
theorem muskingum_nonneg_iff {K X dt : ℝ} (hK : 0 < K)
    (hX0 : 0 ≤ X) (hX : X ≤ 1 / 2) (hdt : 0 < dt) :
    (0 ≤ muskingumC0 K X dt ∧ 0 ≤ muskingumC1 K X dt
      ∧ 0 ≤ muskingumC2 K X dt)
      ↔ 2 * K * X ≤ dt ∧ dt ≤ 2 * K * (1 - X) := by
  have h1X : 0 < 1 - X := by linarith
  have hKX : 0 < 2 * K * (1 - X) := by positivity
  have hden_pos : 0 < muskingumDenominator K X dt := by
    unfold muskingumDenominator
    linarith
  have hden_ne : muskingumDenominator K X dt ≠ 0 := ne_of_gt hden_pos
  have key : ∀ a : ℝ, (0 ≤ a / muskingumDenominator K X dt ↔ 0 ≤ a) := by
    intro a
    constructor
    · intro h
      have h' := mul_nonneg h (le_of_lt hden_pos)
      rwa [div_mul_cancel₀ a hden_ne] at h'
    · intro h
      exact div_nonneg h (le_of_lt hden_pos)
  simp only [muskingumC0, muskingumC1, muskingumC2, key]
  have hC1 : 0 ≤ dt + 2 * K * X := by positivity
  constructor
  · rintro ⟨h0, -, h2⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h0, h2⟩
    exact ⟨by linarith, hC1, by linarith⟩

end EarthScience
