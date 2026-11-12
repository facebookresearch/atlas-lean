/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.Ring

/-!
# Earthquake moment, magnitude, and occurrence models: moment magnitude

## i. Overview

Moment magnitude is `Mw(M) = (2 / 3) * (log₁₀ M - c)` for positive
moment `M`, where `log₁₀ x = Real.log x / Real.log 10` and `c` is the
magnitude zero-point for one fixed moment unit. `c` changes under unit
conversion; both sides of each identity below use the same `c`. Zero
moment is excluded from the logarithm. Energy scaling is a different
empirical relation and is not claimed here.

## ii. Key results

- `EarthScience.momentMagnitude_difference`: `Mw(k * M) - Mw(M) = (2 / 3) * log₁₀ k`.
- `EarthScience.momentMagnitude_scaled`: `Mw(k * M) = Mw(M) + (2 / 3) * log₁₀ k`.
- `EarthScience.momentMagnitude_one`: `Mw(1) = -(2 / 3) * c`.

## iii. Table of contents

- A. Moment-magnitude shift under scaling, and unit moment

## iv. References

- `Real.log_mul`, `Real.log_one` in Mathlib.

## A. Moment-magnitude shift under scaling, and unit moment
-/

@[expose] public section

namespace EarthScience

/-- Moment magnitude: `Mw(M) = (2 / 3) * (log₁₀ M - c)` for positive moment `M`,
with `log₁₀ x = Real.log x / Real.log 10` and a fixed zero-point `c`.
Scaling the moment by `k > 0` shifts the magnitude by `(2 / 3) * log₁₀ k`. -/
theorem momentMagnitude_difference {M k c : ℝ} (hM : 0 < M) (hk : 0 < k) :
    (2 / 3 : ℝ) * (Real.log (k * M) / Real.log 10 - c)
      - (2 / 3 : ℝ) * (Real.log M / Real.log 10 - c)
      = (2 / 3 : ℝ) * (Real.log k / Real.log 10) := by
  have hkm : Real.log (k * M) = Real.log k + Real.log M :=
    Real.log_mul (ne_of_gt hk) (ne_of_gt hM)
  rw [hkm, add_div]
  ring

/-- The same shift, stated as a formula for `Mw (k * M)`. -/
theorem momentMagnitude_scaled {M k c : ℝ} (hM : 0 < M) (hk : 0 < k) :
    (2 / 3 : ℝ) * (Real.log (k * M) / Real.log 10 - c)
      = (2 / 3 : ℝ) * (Real.log M / Real.log 10 - c)
        + (2 / 3 : ℝ) * (Real.log k / Real.log 10) := by
  have hkm : Real.log (k * M) = Real.log k + Real.log M :=
    Real.log_mul (ne_of_gt hk) (ne_of_gt hM)
  rw [hkm, add_div]
  ring

/-- At unit moment (`M = 1`), `Mw(1) = -(2 / 3) * c`. -/
theorem momentMagnitude_one {c : ℝ} :
    (2 / 3 : ℝ) * (Real.log 1 / Real.log 10 - c) = -(2 / 3 : ℝ) * c := by
  rw [Real.log_one, zero_div]
  ring

end EarthScience
