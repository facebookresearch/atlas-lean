/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Ring

/-!
# Earthquake moment, magnitude, and occurrence models: moment magnitude

## i. Overview

Moment magnitude is `Mw(M) = (2 / 3) * (log₁₀ M - c)` for positive
moment `M`, where `log₁₀ x = Real.log x / Real.log 10` and `c` is the
magnitude zero-point for one fixed moment unit. This is the scale of
Hanks and Kanamori (1979), `Mw = (2 / 3) * log₁₀ M₀ - 10.7` with `M₀` in
dyne·cm, with the additive constant moved inside the bracket:
`c = (3 / 2) * 10.7 = 16.05` for dyne·cm. Since `1 N·m = 10⁷ dyne·cm`, the
same scale for `M₀` in N·m has `c = 16.05 - 7 = 9.05`, which the IASPEI
standard `Mw = (log₁₀ M₀ - 9.1) / 1.5` rounds to `c = 9.1`. In general,
measuring the moment in a unit `10ⁿ` times smaller replaces `c` by
`c + n`, so `c` changes under unit conversion; both sides of each identity
below use the same `c`. `momentMagnitude_one` is this normalization: one
moment unit has `Mw = -(2 / 3) * c` (`-10.7` for dyne·cm). Zero moment is
excluded from the logarithm. Energy scaling is a different empirical
relation and is not claimed here.

## ii. Key results

- `EarthScience.momentMagnitude_difference`: `Mw(k * M) - Mw(M) = (2 / 3) * log₁₀ k`.
- `EarthScience.momentMagnitude_scaled`: `Mw(k * M) = Mw(M) + (2 / 3) * log₁₀ k`.
- `EarthScience.momentMagnitude_one`: `Mw(1) = -(2 / 3) * c`.

## iii. Table of contents

- A. Moment-magnitude shift under scaling, and unit moment

## iv. References

- Thomas C. Hanks and Hiroo Kanamori, *A moment magnitude scale*,
  J. Geophys. Res. 84 (B5) (1979), 2348–2350,
  doi:10.1029/JB084iB05p02348 (`M = (2 / 3) log₁₀ M₀ - 10.7`, `M₀` in
  dyne·cm).
- IASPEI Commission on Seismological Observation and Interpretation,
  *Summary of Magnitude Working Group recommendations on standard
  procedures for determining earthquake magnitudes from digital data*
  (2013) (`Mw = (log₁₀ M₀ - 9.1) / 1.5`, `M₀` in N·m).
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
