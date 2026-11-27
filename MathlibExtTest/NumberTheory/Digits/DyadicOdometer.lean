/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.DyadicOdometer

/-! # Tests for dyadic carries, odometer interpolation and the limiting curve -/

namespace MetaMathlibExt.odometer_limitingCurve_eq_neg_takagi

-- Adding one to 0111₂ propagates the carry through three positions.
example : let ω : ℕ → Fin 2 := fun i => if i < 3 then 1 else 0
    dyadicOdometer ω 0 = 0 ∧ dyadicOdometer ω 1 = 0 ∧ dyadicOdometer ω 2 = 0 ∧
      dyadicOdometer ω 3 = 1 ∧ dyadicOdometer ω 4 = 0 := by
  decide

-- Half of the first time step reads half the value of the starting sequence.
example (q : ℂ) : odometerDigitPartialSum q (fun i => if i = 0 then 1 else 0) (1 / 2) =
    q / 2 := by
  have hd : (∑' i : ℕ, (((if i = 0 then 1 else 0 : Fin 2) : ℕ) : ℂ) * q ^ (i + 1)) = q := by
    rw [tsum_eq_single 0 (fun i hi => by simp [hi])]
    simp
  have hf : ⌊(1 / 2 : ℝ)⌋₊ = 0 := Nat.floor_eq_zero.mpr (by norm_num)
  norm_num [odometerDigitPartialSum, hf, Int.fract, hd]
  ring

-- The admissible annulus includes purely imaginary parameters.
example : ∀ᵐ ω ∂dyadicHaar, ∃ (l : ℕ → ℕ) (R : ℕ → ℂ),
    IsStabilizingSeq (3 / 4 * Complex.I) ω l R
      (fun t => -takagiLandsberg (1 / (2 * (3 / 4 * Complex.I))) t) := by
  apply odometer_limitingCurve_eq_neg_takagi
  all_goals norm_num [norm_mul, norm_div]

end MetaMathlibExt.odometer_limitingCurve_eq_neg_takagi
