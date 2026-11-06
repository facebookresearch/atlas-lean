/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LSeries.ArgumentVariation

/-!
# Tests for `argVariationToCriticalLine`

The argument variation of a nonzero constant vanishes, the variation is additive over products
of nonvanishing functions only through `logDeriv`, and the closed form for `π^{-s/2}`.
-/

@[expose] public section

open Complex

namespace ArgumentVariationTest

/-- The definition: the vertical leg `2 → 2 + iT` followed by the horizontal leg
`2 + iT → 1/2 + iT`. -/
example (f : ℂ → ℂ) (T : ℝ) : argVariationToCriticalLine f T =
    (∫ y in (0 : ℝ)..T, logDeriv f (2 + y * I) * I).im +
      (∫ x in (2 : ℝ)..(1 / 2), logDeriv f (x + T * I)).im :=
  rfl

/-- A constant has no argument variation. -/
example (c : ℂ) (T : ℝ) : argVariationToCriticalLine (fun _ => c) T = 0 := by
  simp [argVariationToCriticalLine, logDeriv_const]

/-- At height `0` only the horizontal leg contributes; for `π^{-s/2}` it is real, so the variation
is `0`. -/
example : argVariationToCriticalLine (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2)) 0 = 0 := by
  rw [argVariationToCriticalLine_pi_cpow]
  simp

/-- `π^{-s/2}` at `T = 2`: the variation is `-log π`. -/
example : argVariationToCriticalLine (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2)) 2 =
    -Real.log Real.pi := by
  rw [argVariationToCriticalLine_pi_cpow]
  ring

/-- The `s - 1` factor contributes `π/2 + O(1/T)`. -/
example : (fun T : ℝ => argVariationToCriticalLine (fun s : ℂ => s - 1) T - Real.pi / 2)
    =O[Filter.atTop] (fun T : ℝ => 1 / T) :=
  argVariationToCriticalLine_sub_one_sub_isBigO

/-- The Gamma factor contributes `(T/2) log (T/2) - T/2 + 3π/8 + O(1/T)`. -/
example : (fun T : ℝ => argVariationToCriticalLine (fun s : ℂ => Gamma (s / 2 + 1)) T -
    (T / 2 * Real.log (T / 2) - T / 2 + 3 / 8 * Real.pi)) =O[Filter.atTop] (fun T : ℝ => 1 / T) :=
  argVariationToCriticalLine_Gamma_sub_isBigO

end ArgumentVariationTest
