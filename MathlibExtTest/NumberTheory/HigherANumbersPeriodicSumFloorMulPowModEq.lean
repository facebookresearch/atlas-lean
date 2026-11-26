/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.HigherANumbersPeriodicSumFloorMulPowModEq
import Mathlib.Tactic.NormNum

/-!
# Tests for periodicity of floors of rational multiples of prime powers

These examples apply the floor periodicity theorem at the two delay thresholds.
-/

namespace MathlibExtTest.NumberTheory.HigherANumbersPeriodicSumFloorMulPowModEq

open MetaMathlibExt

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private lemma ten_thirds_parts :
    primeToPNum 5 (10 / 3) = 2 ∧ basePDelay 5 (10 / 3) = -1 := by
  have hnum : (10 / 3 : ℚ).num = 10 :=
    Rat.num_div_eq_of_coprime (by norm_num) (by decide)
  have hden : (10 / 3 : ℚ).den = 3 := by
    have hd : ((10 / 3 : ℚ).den : ℤ) = 3 :=
      Rat.den_div_eq_of_coprime (by norm_num) (by decide)
    omega
  have h10 : multiplicity (5 : ℕ) 10 = 1 :=
    multiplicity_eq_of_dvd_of_not_dvd (by norm_num) (by norm_num)
  have h3 : multiplicity (5 : ℕ) 3 = 0 := multiplicity_eq_zero_of_not_dvd (by norm_num)
  norm_num [primeToPNum, basePDelay, padicValRat_def, padicValInt, Nat.padicValNat_def,
    hnum, hden, h10, h3]

example : ⌊(10 / 3 : ℚ) * (5 : ℚ) ^ (-1 : ℤ)⌋ ≡
    ⌊(10 / 3 : ℚ) * (5 : ℚ) ^ (-1 + basePPeriod 5 (10 / 3) : ℤ)⌋ [ZMOD 2] := by
  have h := (floor_mul_pow_modEq 5 (by norm_num : (0 : ℚ) < 10 / 3)).1 (-1) ?_
  · simpa [ten_thirds_parts.1] using h
  · norm_num [ten_thirds_parts.2]

example : ⌊(10 / 3 : ℚ) * (5 : ℚ) ^ (0 : ℤ)⌋ ≡
    ⌊(10 / 3 : ℚ) * (5 : ℚ) ^ (basePPeriod 5 (10 / 3) : ℤ)⌋ [ZMOD 5] := by
  have h := (floor_mul_pow_modEq 5 (by norm_num : (0 : ℚ) < 10 / 3)).2 0 ?_
  · simpa using h
  · norm_num [ten_thirds_parts.2]

end MathlibExtTest.NumberTheory.HigherANumbersPeriodicSumFloorMulPowModEq
