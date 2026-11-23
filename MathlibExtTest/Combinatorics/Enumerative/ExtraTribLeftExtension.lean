/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.ExtraTribLeftExtension
import MathlibExt.NumberTheory.TribonacciInt

/-! # Tests for the signs of the two-sided Tribonacci sequence -/

namespace MetaMathlibExt.extraTrib_left_extension

private theorem tribonacciInt_isExtraTrib : IsExtraTrib tribonacciInt := by
  have hpos (m : ℕ) : 0 < tribonacci (m + 2) := by
    induction m with
    | zero => decide
    | succ m ih =>
      change 0 < tribonacci (m + 3)
      rw [tribonacci]
      omega
  refine ⟨tribonacciInt_add_three, 1, ?_⟩
  intro n hn
  obtain ⟨m, rfl⟩ := Int.le.dest hn
  rw [Int.add_comm]
  change 0 < tribonacciInt ((m + 1 : ℕ) : ℤ)
  rw [tribonacciInt_nat_eq]
  exact_mod_cast hpos m

-- The triple immediately before the negative term at -3 ends in zero.
example : tribonacciInt (-4) = 0 ∧
    ¬ (0 < tribonacciInt (-6) ∧ 0 < tribonacciInt (-5) ∧ 0 < tribonacciInt (-4)) ∧
    ¬ (tribonacciInt (-6) < 0 ∧ tribonacciInt (-5) < 0 ∧ tribonacciInt (-4) < 0) :=
  ⟨rfl, (extraTrib_left_extension _ tribonacciInt_isExtraTrib).2 (-3) (by decide) (-6)
    (by decide)⟩

end MetaMathlibExt.extraTrib_left_extension
