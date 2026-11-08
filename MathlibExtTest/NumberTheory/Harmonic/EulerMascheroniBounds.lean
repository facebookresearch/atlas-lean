/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Harmonic.EulerMascheroniBounds

@[expose] public section

open Real

/-- At `n = 1` the integer bound is `|1 - γ| ≤ 1`. -/
example :
    |(harmonic 1 : ℝ) - Real.log 1 - Real.eulerMascheroniConstant| ≤ 1 := by
  have h := Real.abs_harmonic_sub_log_sub_eulerMascheroniConstant_le (n := 1) le_rfl
  simpa using h

/-- At `n = 2` the integer bound is `|3 / 2 - log 2 - γ| ≤ 1 / 2`. -/
example :
    |(harmonic 2 : ℝ) - Real.log 2 - Real.eulerMascheroniConstant| ≤ 1 / 2 := by
  have h := Real.abs_harmonic_sub_log_sub_eulerMascheroniConstant_le (n := 2) (by norm_num)
  norm_num [harmonic] at h ⊢
  convert h using 2

/-- At `x = 2` the floor bound is `|3 / 2 - log 2 - γ| ≤ 1`. -/
example :
    |(harmonic ⌊(2 : ℝ)⌋₊ : ℝ) - Real.log 2 - Real.eulerMascheroniConstant| ≤ 1 := by
  have h := Real.abs_harmonic_floor_sub_log_sub_eulerMascheroniConstant_le
    (x := 2) (by norm_num)
  norm_num [harmonic] at h ⊢
  convert h using 2

/-- At `x = 3` the floor bound is `|11 / 6 - log 3 - γ| ≤ 2 / 3`. -/
example :
    |(harmonic ⌊(3 : ℝ)⌋₊ : ℝ) - Real.log 3 - Real.eulerMascheroniConstant| ≤ 2 / 3 := by
  have h := Real.abs_harmonic_floor_sub_log_sub_eulerMascheroniConstant_le
    (x := 3) (by norm_num)
  norm_num [harmonic] at h ⊢
  convert h using 2

/-- The floor–logarithm estimate at `x = 2` is `0 ≤ 1 / 2`. -/
example : Real.log 2 - Real.log (⌊(2 : ℝ)⌋₊ : ℝ) ≤ 1 / 2 := by
  have h := Real.log_sub_log_floor_le (x := 2) (by norm_num)
  rw [show (⌊(2 : ℝ)⌋₊ : ℝ) = 2 by norm_num] at h ⊢
  exact h

end
