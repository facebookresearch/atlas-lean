/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModInverseSwitchingEuclidBezoutCoeffsAbsLe
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

namespace MathlibExtTest.NumberTheory.ModInverseSwitchingEuclidBezoutCoeffsAbsLe

open MathlibExt.NumberTheory.ModInverseSwitchingWanted

/-- Remainders of the Euclidean algorithm on `(5, 3)`. -/
def rTest : ℕ → ℕ
  | 0 => 5
  | 1 => 3
  | 2 => 2
  | _ => 1

/-- Bézout data for `(5, 3)`: `s 1 = 2`, `s 2 = -1` and `s 3 = 1`. -/
def sTest : ℕ → ℤ
  | 0 => 0
  | 1 => 2
  | 2 => -1
  | _ => 1

theorem hseqTest : IsEuclidSwitchSeq rTest sTest 2 := by
  refine ⟨by decide, ?_, ?_, rfl, ?_, rfl, ?_⟩
  · intro i hi
    have hi3 : i ≤ 3 := hi
    clear hi
    interval_cases i <;> decide
  · intro i hi
    interval_cases i <;> decide
  · intro i h1 h2
    interval_cases i
    · exact ⟨1, by decide, by decide⟩
    · exact ⟨1, by decide, by decide⟩
  · intro i h1 h2
    interval_cases i <;> decide

theorem gcd_test : Nat.gcd 5 3 = 1 :=
  (Nat.coprime_primes (by norm_num) (by norm_num)).mpr (by decide)

-- The Euclidean Bézout pair for `(5, 3)` is `(-1, 2)`, smallest in absolute value.
example (x y : ℤ) (hxy : x * 5 + y * 3 = 1) : 1 ≤ |x| ∧ 2 ≤ |y| := by
  have h := euclid_bezout_coeffs_abs_le 5 3 (by decide) (by decide) rTest sTest 2 hseqTest
    (by rw [gcd_test, Nat.div_one]; rfl) (by rw [gcd_test, Nat.div_one]; rfl) x y
    (by simpa [gcd_test] using hxy)
  have e1 : |sTest 2| = 1 := by decide
  have e2 : |sTest 1| = 2 := by decide
  simpa [e1, e2] using h

end MathlibExtTest.NumberTheory.ModInverseSwitchingEuclidBezoutCoeffsAbsLe
