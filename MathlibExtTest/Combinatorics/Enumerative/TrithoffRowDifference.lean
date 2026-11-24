/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.TrithoffRowDifference

/-! # Tests for differences along a Trithoff row -/

namespace MetaMathlibExt.exists_trithoff_row_difference_eq

-- The empty word has no digits contributing to either shifted value.
example : ∃ k : ℕ, (tribonacciValue (List.replicate (k + 1) 0) : ℤ) -
    tribonacciValue (List.replicate k 0) = 0 := by
  simpa [show tribonacciValue [0] = 0 by decide] using
    exists_trithoff_row_difference_eq [] 0 (by simp [IsTribonacciRepr])

-- Multiplying the word 11 by 11 produces 121, including a digit larger than one.
example : tribonacciValue [1, 2, 1] = 9 ∧ ¬ IsTribonacciRepr [1, 2, 1] 9 := by
  unfold IsTribonacciRepr
  decide

example : ∃ k : ℕ, (tribonacciValue (List.replicate (k + 1) 0 ++ [1, 1]) : ℤ) -
    tribonacciValue (List.replicate k 0 ++ [1, 1]) = 9 :=
  exists_trithoff_row_difference_eq [1, 1] 3 (by unfold IsTribonacciRepr; decide)

end MetaMathlibExt.exists_trithoff_row_difference_eq
