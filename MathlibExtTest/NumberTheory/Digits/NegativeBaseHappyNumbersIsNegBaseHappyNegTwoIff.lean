/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.NegativeBaseHappyNumbersIsNegBaseHappyNegTwoIff

/-! # Tests for `isNegBaseHappy_neg_two_iff` -/

namespace MathlibExtTest.NumberTheory.Digits.NegativeBaseHappyNumbersIsNegBaseHappyNegTwoIff

example : MetaMathlibExt.IsNegBaseHappy (-2) 4 :=
  (MetaMathlibExt.isNegBaseHappy_neg_two_iff.2 4).mpr (by decide)

example : ¬ MetaMathlibExt.IsNegBaseHappy (-2) 5 := by
  intro h
  exact absurd ((MetaMathlibExt.isNegBaseHappy_neg_two_iff.2 5).mp h) (by decide)

example : ∃ m : ℤ, MetaMathlibExt.IsNegBaseHappy (-2) m ∧
    MetaMathlibExt.IsNegBaseHappy (-2) (m + 3) := by
  obtain ⟨n, hn⟩ := MetaMathlibExt.isNegBaseHappy_neg_two_iff.1
  have h0 : MetaMathlibExt.IsNegBaseHappy (-2) n := by
    simpa using hn 0
  have h1 : MetaMathlibExt.IsNegBaseHappy (-2) (n + 3) := by
    simpa using hn 1
  exact ⟨n, h0, h1⟩

end MathlibExtTest.NumberTheory.Digits.NegativeBaseHappyNumbersIsNegBaseHappyNegTwoIff
