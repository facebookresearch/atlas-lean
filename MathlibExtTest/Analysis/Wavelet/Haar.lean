/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Wavelet.Haar

/-!
# Tests for the Haar function
-/

open Set
open MathlibExt.Analysis.Wavelet.Haar

namespace MathlibExtTest.Analysis.Wavelet.Haar

example : haarFunction (1 / 4) = 1 := haarFunction_eq_one ⟨by norm_num, by norm_num⟩

example : haarFunction (3 / 4) = -1 := haarFunction_eq_neg_one ⟨by norm_num, by norm_num⟩

example : haarFunction 2 = 0 := haarFunction_eq_zero fun h => by norm_num at h

/-- At scale `j = 0` and translation `k = 0` the Haar system is the Haar function itself. -/
example (x : ℝ) : haarSystem 0 0 x = haarFunction x := by simp [haarSystem]

/-- The Haar function at scale `2` takes the value `√2` on `[0, 1/4)`. -/
example : haarSystem 1 0 (1 / 8) = Real.sqrt 2 := by
  rw [haarSystem, haarFunction_eq_one ⟨by norm_num, by norm_num⟩, mul_one,
    Real.sqrt_eq_rpow]
  norm_num

/-- Orthonormality instances: two scales, two translations, and the unit norm. -/
example : ∫ x, haarSystem 0 0 x * haarSystem 1 0 x = 0 := by
  rw [integral_haarSystem_mul_haarSystem]; simp

example : ∫ x, haarSystem 2 1 x * haarSystem 2 3 x = 0 := by
  rw [integral_haarSystem_mul_haarSystem]; simp

example : ∫ x, haarSystem (-3) 5 x * haarSystem (-3) 5 x = 1 := by
  rw [integral_haarSystem_mul_haarSystem]; simp

end MathlibExtTest.Analysis.Wavelet.Haar
