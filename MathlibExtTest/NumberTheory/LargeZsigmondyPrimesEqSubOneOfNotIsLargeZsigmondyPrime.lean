/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime
import MathlibExt.NumberTheory.LargeZsigmondyPrimesEqSubOneOfNotIsLargeZsigmondyPrime

/-! # Tests for `MathlibExt.NumberTheory.LargeZsigmondyPrimesEqSubOneOfNotIsLargeZsigmondyPrime` -/

namespace MathlibExtTest.NumberTheory.LargeZsigmondyPrimesEqSubOneOfNotIsLargeZsigmondyPrime

open MetaMathlibExt

-- `3` is a primitive prime divisor of `2 ^ 2 - 1 ^ 2` that is not large, so `2 = 3 - 1`.
example : (2 : ℕ) = 3 - 1 := by
  have hq : IntegerSequence.IsPrimitivePrimeDivisor
      (fun m => (2 : ℤ) ^ m - (1 : ℤ) ^ m) 2 3 := by
    refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
    intro s hs hs2
    interval_cases s; norm_num
  have hql : ¬ IsLargeZsigmondyPrime 2 1 2 3 := by
    intro h
    rw [IsLargeZsigmondyPrime] at h
    obtain ⟨-, h | h⟩ := h
    · norm_num at h
    · norm_num at h
  exact eq_sub_one_of_not_isLargeZsigmondyPrime (by norm_num) (by norm_num) (by decide)
    (by norm_num) hq hql

-- A non-large Zsigmondy prime is one more than the exponent.
example {a b n q : ℕ} (hb : 0 < b) (hba : b < a) (hcop : a.Coprime b) (hn : 2 ≤ n)
    (hq : IntegerSequence.IsPrimitivePrimeDivisor
      (fun m => (a : ℤ) ^ m - (b : ℤ) ^ m) n q)
    (hql : ¬ IsLargeZsigmondyPrime a b n q) : q = n + 1 := by
  have h := eq_sub_one_of_not_isLargeZsigmondyPrime hb hba hcop hn hq hql
  have hq2 : 2 ≤ q := hq.prime.two_le
  omega

end MathlibExtTest.NumberTheory.LargeZsigmondyPrimesEqSubOneOfNotIsLargeZsigmondyPrime
