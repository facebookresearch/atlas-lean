/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GoldenRatioLeftFactorialLambertKurepaPartialIntegralLambertSequenceBounds
import MathlibExt.NumberTheory.GoldenRatioLeftFactorialLambertTwoParameterBounds

/-! # Tests for the two-parameter Lambert bounds -/

namespace MathlibExtTest.NumberTheory.GoldenRatioLeftFactorialLambertTwoParameterBounds

open MetaMathlibExt Real

-- The lower-branch comparison includes the endpoint `-1`.
example : lambertMap (-1) < lambertMap (-2) :=
  lambertMap_strictAntiOn_Iic (by norm_num [Set.mem_Iic]) (by norm_num [Set.mem_Iic])
    (by norm_num)

-- At `n = 3`, the cutoff `2` normalizes to a target other than `4 / 7`.
example : (2 : ℝ) ^ (2 : ℕ) * exp (-2) = (2 * exp (-1)) ^ (2 : ℕ) := by
  have hroot : ((2 * exp (-1)) ^ (2 : ℕ)) ^ (1 / 2 : ℝ) = 2 * exp (-1) := by
    rw [show (1 / 2 : ℝ) = ((2 : ℕ) : ℝ)⁻¹ by norm_num]
    exact pow_rpow_inv_natCast (by positivity) (by decide)
  have h := lambertCutoff_pow_mul_exp 3 (by decide) 2
    (c := (2 * exp (-1)) ^ (2 : ℕ)) (by positivity) (by
      rw [show ((3 : ℕ) : ℝ) - 1 = 2 by norm_num, hroot,
        show -(2 : ℝ) / 2 = -1 by norm_num, lambertMap.eq_def]
      ring)
  exact h

-- At the smallest allowed `n` and `m`, the actual lower-branch cutoff puts the integral in (33, 34).
example : ∃ A : ℝ, 4 ≤ A ∧
    lambertMap (-A / 4) = -(1 / 4) * (4 / 7 : ℝ) ^ (1 / 4 : ℝ) ∧
    kurepaPartialIntegral 5 A ∈ Set.Ioo 33 34 := by
  obtain ⟨A, hA, hW⟩ := exists_lambertSequence (n := 5) (by decide)
    (c := 4 / 7) (by norm_num) (by norm_num)
  have hb := kurepaPartialIntegral_lambertSequence_two_bounds 5 1 (by decide) le_rfl A hA
    (by norm_num at hW ⊢; exact hW)
  rw [show ((5 : ℕ) : ℝ) - 1 = 4 by norm_num] at hA hW
  norm_num [Finset.sum_range_succ, Nat.factorial] at hb
  exact ⟨A, hA, hW, by linarith [hb.2], hb.1⟩

-- Doubling `m` gives an actual cutoff with integral in the narrower interval (33.5, 34).
example : ∃ A : ℝ, 4 ≤ A ∧
    lambertMap (-A / 4) = -(1 / 4) * (4 / 14 : ℝ) ^ (1 / 4 : ℝ) ∧
    kurepaPartialIntegral 5 A ∈ Set.Ioo (67 / 2) 34 := by
  obtain ⟨A, hA, hW⟩ := exists_lambertSequence (n := 5) (by decide)
    (c := 4 / 14) (by norm_num) (by norm_num)
  have hb := kurepaPartialIntegral_lambertSequence_two_bounds 5 2 (by decide) (by decide) A hA
    (by norm_num at hW ⊢; exact hW)
  rw [show ((5 : ℕ) : ℝ) - 1 = 4 by norm_num] at hA hW
  norm_num [Finset.sum_range_succ, Nat.factorial] at hb
  exact ⟨A, hA, hW, by linarith [hb.2], hb.1⟩

end MathlibExtTest.NumberTheory.GoldenRatioLeftFactorialLambertTwoParameterBounds
