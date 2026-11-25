/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.IntervalCases
import MathlibExt.NumberTheory.Cyclotomic.DvdHomogenizedCyclotomicOfIsPrimitivePrimeDivisor

/-! # Tests for Zsigmondy primes dividing homogenized cyclotomic values -/

open MetaMathlibExt

-- The homogenized cyclotomic value at `(2, 1)` and index `3` is `7`.
example : homogenizedCyclotomic 3 (2 : ℤ) 1 = 7 := by
  rw [homogenizedCyclotomic_one_right]
  norm_num [Polynomial.cyclotomic_three]

-- `7` is a primitive prime divisor of `2 ^ 3 - 1 ^ 3`, so it divides `Φ_3(2, 1)`.
example : (7 : ℤ) ∣ homogenizedCyclotomic 3 2 1 := by
  have hp : IntegerSequence.IsPrimitivePrimeDivisor (fun m => (2 : ℤ) ^ m - (1 : ℤ) ^ m) 3 7 := by
    refine ⟨by decide, by norm_num, by norm_num, by norm_num, ?_⟩
    intro s hs hs3
    interval_cases s <;> norm_num
  exact dvd_homogenizedCyclotomic_of_isPrimitivePrimeDivisor (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hp

-- `5` is a primitive prime divisor of `3 ^ 2 - 2 ^ 2`, so it divides `Φ_2(3, 2) = 5`.
example : (5 : ℤ) ∣ homogenizedCyclotomic 2 3 2 := by
  have hp : IntegerSequence.IsPrimitivePrimeDivisor (fun m => (3 : ℤ) ^ m - (2 : ℤ) ^ m) 2 5 := by
    refine ⟨by decide, by norm_num, by norm_num, by norm_num, ?_⟩
    intro s hs hs2
    have hs1 : s = 1 := by omega
    subst hs1
    norm_num
  exact dvd_homogenizedCyclotomic_of_isPrimitivePrimeDivisor (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hp
