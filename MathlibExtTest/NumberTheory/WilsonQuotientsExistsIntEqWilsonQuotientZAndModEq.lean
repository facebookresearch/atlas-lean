/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.WilsonQuotientsExistsIntEqWilsonQuotientZAndModEq

/-! # Tests for `MathlibExt.NumberTheory.WilsonQuotientsExistsIntEqWilsonQuotientZAndModEq` -/

namespace MathlibExtTest.NumberTheory.WilsonQuotientsExistsIntEqWilsonQuotientZAndModEq

open MathlibExt.NumberTheory.WilsonQuotientsWanted

-- At the composite index `6` the witness is `1` modulo `6`.
example : ∃ z : ℤ, (z : ℚ) = wilsonQuotientZ 6 ∧ z ≡ 1 [ZMOD 6] := by
  obtain ⟨z, hz, hcomp, -⟩ := exists_int_eq_wilsonQuotientZ_and_modEq 6 (by decide)
  exact ⟨z, hz, hcomp (by decide)⟩

-- At the prime index `5` the witness is `-1` modulo `5`.
example : ∃ z : ℤ, (z : ℚ) = wilsonQuotientZ 5 ∧ z ≡ -1 [ZMOD 5] := by
  obtain ⟨z, hz, -, hprime⟩ := exists_int_eq_wilsonQuotientZ_and_modEq 5 (by decide)
  exact ⟨z, hz, hprime (Or.inr (by decide))⟩

-- Direct evaluation cross-check: `Z 6 = 1`.
example : wilsonQuotientZ 6 = 1 := by
  have f3 : Nat.factorial 3 = 6 := rfl
  have f4 : Nat.factorial 4 = 24 := rfl
  have f5 : Nat.factorial 5 = 120 := rfl
  norm_num [wilsonQuotientZ, wilsonQuotientM, Finset.sum_range_succ, Finset.sum_range_zero,
    f3, f4, f5]

-- The integer witness at `n = 6` must equal `1`.
example (z : ℤ) (hz : (z : ℚ) = wilsonQuotientZ 6) : z = 1 := by
  have f3 : Nat.factorial 3 = 6 := rfl
  have f4 : Nat.factorial 4 = 24 := rfl
  have f5 : Nat.factorial 5 = 120 := rfl
  have h6 : wilsonQuotientZ 6 = 1 := by
    norm_num [wilsonQuotientZ, wilsonQuotientM, Finset.sum_range_succ, Finset.sum_range_zero,
      f3, f4, f5]
  have hcast : (z : ℚ) = 1 := by rw [hz, h6]
  exact_mod_cast hcast

end MathlibExtTest.NumberTheory.WilsonQuotientsExistsIntEqWilsonQuotientZAndModEq
